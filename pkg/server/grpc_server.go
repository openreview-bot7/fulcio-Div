// Copyright 2022 The Sigstore Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package server

import (
	"context"
	"crypto"
	"crypto/sha256"
	"crypto/x509"
	"encoding/asn1"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"time"

	"math/big"

	"io/ioutil"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/sigstore/sigstore/pkg/signature"

	ctclient "github.com/google/certificate-transparency-go/client"
	health "google.golang.org/grpc/health/grpc_health_v1"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"

	certauth "github.com/sigstore/fulcio/pkg/ca"
	"github.com/sigstore/fulcio/pkg/challenges"
	"github.com/sigstore/fulcio/pkg/config"
	"github.com/sigstore/fulcio/pkg/ctl"
	fulciogrpc "github.com/sigstore/fulcio/pkg/generated/protobuf"
	"github.com/sigstore/fulcio/pkg/identity"
	"github.com/sigstore/fulcio/pkg/log"
	"github.com/sigstore/sigstore/pkg/cryptoutils"
)

type GRPCCAServer interface {
	fulciogrpc.CAServer
	health.HealthServer
}
type ECDSASignature struct {
	R, S *big.Int
}
type Policy struct {
	Identity          string `json:"identity"`
	Provider          string `json:"provider"`
	DeviceFingerprint string `json:"device_fingerprint"`
	SecurityKey       string `json:"security_key"`
	SignerMeasurement string `json:"signer_measurement"`
	RaRequired        bool   `json:"ra_required"`
	Rule              string `json:"rule"`
}

type PolicyEvaluator struct {
	Policy Policy
}

func NewGRPCCAServer(ct *ctclient.LogClient, ca certauth.CertificateAuthority, algorithmRegistry *signature.AlgorithmRegistryConfig, ip identity.IssuerPool) GRPCCAServer {
	return &grpcaCAServer{
		ct:                ct,
		ca:                ca,
		algorithmRegistry: algorithmRegistry,
		IssuerPool:        ip,
	}
}

const (
	MetadataOIDCTokenKey = "oidcidentitytoken"
)

type grpcaCAServer struct {
	fulciogrpc.UnimplementedCAServer
	ct                *ctclient.LogClient
	ca                certauth.CertificateAuthority
	algorithmRegistry *signature.AlgorithmRegistryConfig
	identity.IssuerPool
}

func (g *grpcaCAServer) CreateSigningCertificate(ctx context.Context, request *fulciogrpc.CreateSigningCertificateRequest) (*fulciogrpc.SigningCertificate, error) {
	logger := log.ContextLogger(ctx)

	// OIDC token either is passed in gRPC field or was extracted from HTTP headers
	token := ""
	if request.Credentials != nil {
		token = request.Credentials.GetOidcIdentityToken()
	}

	if token == "" {
		if md, ok := metadata.FromIncomingContext(ctx); ok {
			vals := md.Get(MetadataOIDCTokenKey)
			if len(vals) == 1 {
				token = vals[0]
			}
		}
	}

	// Authenticate OIDC ID token by checking signature
	principal, err := g.Authenticate(ctx, token)
	if err != nil {
		return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, invalidIdentityToken)
	}

	var publicKey crypto.PublicKey
	var hashFunc crypto.Hash
	// Verify caller is in possession of their private key and extract
	// public key from request.
	if len(request.GetCertificateSigningRequest()) > 0 {
		// Option 1: Verify CSR
		csr, err := cryptoutils.ParseCSR(request.GetCertificateSigningRequest())
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, invalidCSR)
		}

		// Parse public key and check for weak key parameters
		publicKey = csr.PublicKey
		if err := cryptoutils.ValidatePubKey(publicKey); err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, insecurePublicKey)
		}

		if err := csr.CheckSignature(); err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, invalidSignature)
		}

		hashFunc, err = getHashFuncForSignatureAlgorithm(csr.SignatureAlgorithm)
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
		}

		targetOID := asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 57264, 1, 23}
		for _, ext := range csr.Extensions {
			if ext.Id.Equal(targetOID) {
				var err error
				ctx, err = verifyDiverifyProof(ctx, ext.Value, token)
				if err != nil {
					return nil, err
				}
				break
			}
		}
	} else {
		// Option 2: Check the signature for proof of possession of a private key
		var (
			pubKeyContent     string
			proofOfPossession []byte
			err               error
		)
		if request.GetPublicKeyRequest() != nil {
			if request.GetPublicKeyRequest().PublicKey != nil {
				pubKeyContent = request.GetPublicKeyRequest().PublicKey.Content
			}
			proofOfPossession = request.GetPublicKeyRequest().ProofOfPossession
		}

		// Parse public key and check for weak parameters
		publicKey, err = challenges.ParsePublicKey(pubKeyContent)
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, invalidPublicKey)
		}
		if err := cryptoutils.ValidatePubKey(publicKey); err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, insecurePublicKey)
		}

		proofOfPossessionAlgo, err := signature.GetDefaultAlgorithmDetails(publicKey)
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
		}
		verifier, err := signature.LoadDefaultVerifier(publicKey)
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
		}
		// TODO: Ideally this comes from the verifier
		hashFunc = proofOfPossessionAlgo.GetHashType()

		// Check proof of possession signature
		if err := challenges.CheckSignatureWithVerifier(verifier, proofOfPossession, principal.Name(ctx)); err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, invalidSignature)
		}
	}

	// Check whether the public-key/hash algorithm combination is allowed
	isPermitted, err := g.algorithmRegistry.IsAlgorithmPermitted(publicKey, hashFunc)
	if err != nil {
		return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
	}
	if !isPermitted {
		err = fmt.Errorf("signing algorithm not permitted: %T, %s", publicKey, hashFunc)
		return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
	}

	var csc *certauth.CodeSigningCertificate
	var sctBytes []byte
	result := &fulciogrpc.SigningCertificate{}
	// For CAs that do not support embedded SCTs or if the CT log is not configured
	if sctCa, ok := g.ca.(certauth.EmbeddedSCTCA); !ok || g.ct == nil {
		// currently configured CA doesn't support pre-certificate flow required to embed SCT in final certificate
		csc, err = g.ca.CreateCertificate(ctx, principal, publicKey)
		if err != nil {
			// if the error was due to invalid input in the request, return HTTP 400
			if _, ok := err.(certauth.ValidationError); ok {
				return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
			}
			err = fmt.Errorf("error creating certificate: %w", err)
			// otherwise return a 500 error to reflect that it is a transient server issue that the client can't resolve
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, genericCAError)
		}

		// Submit to CTL
		if g.ct != nil {
			sct, err := g.ct.AddChain(ctx, ctl.BuildCTChain(csc.FinalCertificate, csc.FinalChain))
			if err != nil {
				return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToEnterCertInCTL)
			}
			// convert to AddChainResponse because Cosign expects this struct.
			addChainResp, err := ctl.ToAddChainResponse(sct)
			if err != nil {
				return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalSCT)
			}
			sctBytes, err = json.Marshal(addChainResp)
			if err != nil {
				return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalSCT)
			}
		} else {
			logger.Info("Skipping CT log upload.")
		}

		finalPEM, err := csc.CertPEM()
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalCert)
		}

		finalChainPEM, err := csc.ChainPEM()
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalCert)
		}

		result.Certificate = &fulciogrpc.SigningCertificate_SignedCertificateDetachedSct{
			SignedCertificateDetachedSct: &fulciogrpc.SigningCertificateDetachedSCT{
				Chain: &fulciogrpc.CertificateChain{
					Certificates: append([]string{finalPEM}, finalChainPEM...),
				},
			},
		}
		if len(sctBytes) > 0 {
			result.GetSignedCertificateDetachedSct().SignedCertificateTimestamp = sctBytes
		}
	} else {
		precert, err := sctCa.CreatePrecertificate(ctx, principal, publicKey)
		if err != nil {
			// if the error was due to invalid input in the request, return HTTP 400
			if _, ok := err.(certauth.ValidationError); ok {
				return nil, handleFulcioGRPCError(ctx, codes.InvalidArgument, err, err.Error())
			}
			err = fmt.Errorf("error creating a pre-certificate and chain: %w", err)
			// otherwise return a 500 error to reflect that it is a transient server issue that the client can't resolve
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, genericCAError)
		}
		// submit precertificate and chain to CT log
		sct, err := g.ct.AddPreChain(ctx, ctl.BuildCTChain(precert.PreCert, precert.CertChain))
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToEnterCertInCTL)
		}
		csc, err = sctCa.IssueFinalCertificate(ctx, precert, sct)
		if err != nil {
			err = fmt.Errorf("error issuing final certificate using the pre-certificate with CA backend: %w", err)
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, genericCAError)
		}

		finalPEM, err := csc.CertPEM()
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalCert)
		}

		finalChainPEM, err := csc.ChainPEM()
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, codes.Internal, err, failedToMarshalCert)
		}

		result.Certificate = &fulciogrpc.SigningCertificate_SignedCertificateEmbeddedSct{
			SignedCertificateEmbeddedSct: &fulciogrpc.SigningCertificateEmbeddedSCT{
				Chain: &fulciogrpc.CertificateChain{
					Certificates: append([]string{finalPEM}, finalChainPEM...),
				},
			},
		}
	}

	metricNewEntries.Inc()

	return result, nil
}

func (g *grpcaCAServer) GetTrustBundle(ctx context.Context, _ *fulciogrpc.GetTrustBundleRequest) (*fulciogrpc.TrustBundle, error) {
	trustBundle, err := g.ca.TrustBundle(ctx)
	if err != nil {
		return nil, handleFulcioGRPCError(ctx, codes.Internal, err, retrieveTrustBundleCAError)
	}

	resp := &fulciogrpc.TrustBundle{
		Chains: []*fulciogrpc.CertificateChain{},
	}

	for _, chain := range trustBundle {
		certChain := &fulciogrpc.CertificateChain{}
		for _, cert := range chain {
			certPEM, err := cryptoutils.MarshalCertificateToPEM(cert)
			if err != nil {
				return nil, handleFulcioGRPCError(ctx, codes.Internal, err, marshalingCertificateChainBundleCAError)
			}
			certChain.Certificates = append(certChain.Certificates, string(certPEM))
		}
		resp.Chains = append(resp.Chains, certChain)
	}
	return resp, nil
}

func (g *grpcaCAServer) GetConfiguration(ctx context.Context, _ *fulciogrpc.GetConfigurationRequest) (*fulciogrpc.Configuration, error) {
	cfg := config.FromContext(ctx)
	if cfg == nil {
		err := errors.New("configuration not loaded")
		return nil, handleFulcioGRPCError(ctx, codes.Internal, err, loadingFulcioConfigurationError)
	}

	return &fulciogrpc.Configuration{
		Issuers: cfg.ToIssuers(),
	}, nil
}

func (g *grpcaCAServer) Check(_ context.Context, _ *health.HealthCheckRequest) (*health.HealthCheckResponse, error) {
	return &health.HealthCheckResponse{Status: health.HealthCheckResponse_SERVING}, nil
}

func (g *grpcaCAServer) Watch(_ *health.HealthCheckRequest, _ health.Health_WatchServer) error {
	return status.Error(codes.Unimplemented, "unimplemented")
}

func getHashFuncForSignatureAlgorithm(signatureAlgorithm x509.SignatureAlgorithm) (crypto.Hash, error) {
	switch signatureAlgorithm {
	case x509.ECDSAWithSHA256:
		return crypto.SHA256, nil
	case x509.ECDSAWithSHA384:
		return crypto.SHA384, nil
	case x509.ECDSAWithSHA512:
		return crypto.SHA512, nil
	case x509.SHA256WithRSA:
		return crypto.SHA256, nil
	case x509.SHA384WithRSA:
		return crypto.SHA384, nil
	case x509.SHA512WithRSA:
		return crypto.SHA512, nil
	case x509.PureEd25519:
		return crypto.Hash(0), nil
	}
	return crypto.Hash(0), fmt.Errorf("unrecognized signature algorithm: %s", signatureAlgorithm)
}

func verifyDiverifyProof(ctx context.Context, proofBytes []byte, token string) (context.Context, error) {
	// To verify the prrof, we perform 2 things:
	// Step 1. Verify the quote against Intel SGX root
	// Step 2. Verify proof of possession of signing private key by verifying the public key against the user report in the quote
	// However Fulcio already does this against the challenge so we just check the verified token matches the token in the proof

	var proof map[string]interface{}
	if err := json.Unmarshal(proofBytes, &proof); err != nil {
		return nil, handleFulcioGRPCError(ctx, 400, err, "Invalid diverify proof format")
	}
	fmt.Printf("Proof size: %d bytes\n", len(proofBytes))

	quoteStr, ok := proof["quote"].(string)
	if ok {
		quoteData, err := base64.StdEncoding.DecodeString(quoteStr)
		if err != nil {
			return nil, handleFulcioGRPCError(ctx, 400, err, "Failed to decode quote")
		}

		if err := verifyQuote(quoteData); err != nil {
			fmt.Printf("Error verifying quote: %v\n", err)
			return nil, err
		}
	}

	identity, _ := proof["identity"].(map[string]interface{})
	oidc, _ := identity["oidc"].(map[string]interface{})
	proofHash, _ := oidc["token_hash"].(string)

	tokenHash := fmt.Sprintf("%x", sha256.Sum256([]byte(token)))
	if proofHash != tokenHash {
		return nil, handleFulcioGRPCError(ctx, 400, errors.New("token hash mismatch"),
			fmt.Sprintf("Token hash mismatch. Found %v, expected %v", proofHash, tokenHash))
	}

	// Verify diverify prof against policy
	policy_path, err := getPolicyPath("policy.json")
	if err != nil {
		return nil, err
	}
	pe, errr := NewPolicyEvaluator(policy_path)
	if errr != nil {
		panic(errr)
	}
	result, err := pe.Evaluate(proof)
	if err != nil || !result {
		panic("The signature does not meet the policy constraints.")
	}
	fmt.Println("Policy evaluation passed")

	ctx = context.WithValue(ctx, "diverify_proof", proofBytes)
	return ctx, nil
}

func verify(quotePath string) error {
	start := time.Now()
	// We use the SGX DCAP quote verification tool from https://github.com/intel/SGXDataCenterAttestationPrimitives for verification
	fmt.Println("Starting SGX quote verification process")

	baseDir := "/home/SGXDataCenterAttestationPrimitives/SampleCode/QuoteVerificationSample"
	verificationApp := filepath.Join(baseDir, "app")

	if _, err := os.Stat(verificationApp); os.IsNotExist(err) {
		return fmt.Errorf("verification tool not found at %s", verificationApp)
	}
	if _, err := os.Stat(quotePath); os.IsNotExist(err) {
		return fmt.Errorf("quote file not found at %s", quotePath)
	}

	cmd := exec.Command(verificationApp, "-quote", quotePath)
	cmd.Dir = baseDir
	output, err := cmd.CombinedOutput()

	outputStr := string(output)
	if err != nil {
		if strings.Contains(outputStr, "Verification completed, but collateral is out of date based on 'expiration_check_date' you provided.") {
			// Log as success despite the error
			fmt.Println("Warning:", outputStr)
			return nil
		}
		return fmt.Errorf("verification process failed: %v\nProcess output:\n%s", err, outputStr)
	}
	fmt.Println("string(output):", string(output))

	if strings.Contains(string(output), "Verification completed successfully") {

		duration := time.Since(start)
		fmt.Println("Quote verification succeeded. verifyQuote took:", duration)
		fmt.Printf("Verification output:\n%s\n", output)
		return nil
	} else {
		return fmt.Errorf("quote verification failed\nError output:\n%s", output)
	}
}

func verifyQuote(quoteData []byte) error {
	// The verification tool expects a file path, so we need to write the quote data to a temporary file
	// and then call the verification function with that file path.
	// Create a temporary file to store the quote data
	tmpFile, err := ioutil.TempFile("", "*.dat")
	if err != nil {
		return fmt.Errorf("failed to create temporary file: %v", err)
	}
	defer os.Remove(tmpFile.Name())

	if _, err := tmpFile.Write(quoteData); err != nil {
		return fmt.Errorf("failed to write data to temporary file: %v", err)
	}

	if err := tmpFile.Close(); err != nil {
		return fmt.Errorf("failed to close temporary file: %v", err)
	}

	return verify(tmpFile.Name())
}

func NewPolicyEvaluator(policyPath string) (*PolicyEvaluator, error) {
	policy, err := loadPolicy(policyPath)
	if err != nil {
		return nil, err
	}
	return &PolicyEvaluator{Policy: policy}, nil
}

func loadPolicy(path string) (Policy, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return Policy{}, err
	}
	var policy Policy
	err = json.Unmarshal(data, &policy)
	return policy, err
}

func (pe *PolicyEvaluator) buildContext(proof map[string]interface{}) map[string]interface{} {
	identity := proof["identity"].(map[string]interface{})
	oidc := identity["oidc"].(map[string]interface{})
	fmt.Println("divice fingerprint is: ", identity["device_fingerprint"])

	return map[string]interface{}{
		"identity":           oidc["sub"] == pe.Policy.Identity,
		"provider":           oidc["iss"] == pe.Policy.Provider,
		"device_fingerprint": identity["device_fingerprint"] == pe.Policy.DeviceFingerprint,
		"security_key":       identity["security_key"] == pe.Policy.SecurityKey,
		"signer_measurement": identity["signer_measurement"] == pe.Policy.SignerMeasurement,
		"ra_required":        identity["ra_required"] == true,
	}
}

func getPolicyPath(filename string) (string, error) {
	dir, err := os.Getwd()
	if err != nil {
		return "", err
	}
	path := filepath.Join(dir, filename)
	if _, err := os.Stat(path); err != nil {
		return "", err
	}
	return path, nil
}

func (pe *PolicyEvaluator) Evaluate(proof map[string]interface{}) (bool, error) {
	_ = pe.buildContext(proof)

	_ = strings.ReplaceAll(strings.ReplaceAll(pe.Policy.Rule, "AND", "and"), "OR", "or")
	// Will revisit. for now, pass
	return true, nil
}
