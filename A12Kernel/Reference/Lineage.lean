import A12Kernel.Basic
import Lean.Data.Json.FromToJson.Basic

/-! # A12Kernel.Reference.Lineage — reference-semantics compatibility history

The normalized wire shape and the modeled kernel version can remain stable while the executable reference account is corrected. This module keeps the current identity separate from immutable historical shipment identities and supplies the readable lineage mirror checked by the process gate.
-/

namespace A12Kernel.Reference.Lineage

open Lean

def schemaVersion : Nat := 1

structure CompatibilityIdentity where
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  deriving Repr, DecidableEq

/-- The complete identity of one shipped capability. Compatibility versions alone do not
identify an operation, and historical material must not inherit either value from current
support metadata. -/
structure CapabilityIdentity where
  suiteId : String
  operation : String
  compatibility : CompatibilityIdentity
  deriving Repr, DecidableEq

def historicalV0_2_0 : CompatibilityIdentity := {
  referenceSemanticsVersion := "0.2.0"
  protocolVersion := 1
  manifestSchemaVersion := 2
  kernelBehaviorVersion := "30.8.1" }

def current : CompatibilityIdentity := {
  referenceSemanticsVersion := "0.3.0"
  protocolVersion := 1
  manifestSchemaVersion := 2
  kernelBehaviorVersion := "30.8.1" }

def historicalFlatCapability : CapabilityIdentity := {
  suiteId := "flat-validation-empty-logic-v1"
  operation := "flatValidation.evaluateFull"
  compatibility := historicalV0_2_0 }

def currentFlatCapability : CapabilityIdentity := {
  suiteId := "flat-validation-empty-logic-v2"
  operation := "flatValidation.evaluateFull"
  compatibility := current }

def historicalCorrelationCapability : CapabilityIdentity := {
  suiteId := "single-group-correlation-v1"
  operation := "singleGroupCorrelation.firingRows"
  compatibility := historicalV0_2_0 }

def currentCorrelationCapability : CapabilityIdentity := {
  suiteId := "single-group-correlation-v2"
  operation := "singleGroupCorrelation.firingRows"
  compatibility := current }

def historicalReferenceSemanticsVersion : String := historicalV0_2_0.referenceSemanticsVersion

def currentReferenceSemanticsVersion : String := current.referenceSemanticsVersion

def historicalReferenceRevision : String :=
  "9fa50276f5fb70dcd879b0a9712c8d69c0868967"

def historicalSupportManifest : String := "reference/supported-fragment-v1.json"

def currentSupportManifest : String := "reference/supported-fragment-v2.json"

def historicalFlatSuiteId : String := historicalFlatCapability.suiteId

def currentFlatSuiteId : String := currentFlatCapability.suiteId

def historicalCorrelationSuiteId : String := historicalCorrelationCapability.suiteId

def currentCorrelationSuiteId : String := currentCorrelationCapability.suiteId

def separatingRequest : String :=
  "examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json"

def separatingRequestSha256 : String :=
  "f4fd1aa8f9e740e6799192250659765f9c10d725565ea7e32cf68f24e8e87005"

def separatingCurrentResponse : String :=
  "examples/reference-cli/empty-unsigned-number-not-equal-negative.response.json"

def historicalArtifactLock : String :=
  "reference/reference-semantics-0.2.0.lock.json"

def historicalArtifactLockSha256 : String :=
  "75636af6d8bca17aa0ab4f1528597c5105d32eb0ecb23cc1f3426c7e33474473"

def historicalArtifactCount : Nat := 152

structure FrozenArtifact where
  path : String
  sha256 : String
  deriving Repr, DecidableEq

def historicalSeparatingReplay : FrozenArtifact := {
  path := "reference/reference-semantics-0.2.0-separating-replay.json"
  sha256 := "bd0148e39019c8773f57e7904c01e10c19b33b9cbcae7f498e9eacc50a6d060a" }

def postRevisionHistoricalArtifacts : List FrozenArtifact := [historicalSeparatingReplay]

def frozenHistoricalArtifacts : List FrozenArtifact := [
  { path := historicalArtifactLock,
    sha256 := historicalArtifactLockSha256 },
  { path := historicalSupportManifest,
    sha256 := "89e47bda4ee54ac1f80f3bba004e85c27b0cb31c5d97fda1869727cf358e3f17" },
  { path := "reference/flat-validation-empty-logic-v1.capability.json",
    sha256 := "52708f38e3d72e6d0939c00438baf1abdd3b34df31fbb23f8dea0bac86fef3c1" },
  { path := "reference/flat-validation-empty-logic-v1.conformance.json",
    sha256 := "a71b70dfd832ed607c171a4d9139d76663ebb224c63f41059cfbd5ea272f3c8c" },
  { path := "reference/flat-validation-empty-logic-v1.generated-differential-v1.json",
    sha256 := "897dca670bf9fcb6d0cff7cbcb6ce01fd6feb1c41187712928d9f0edcdbe6f87" },
  { path := "reference/flat-validation-empty-logic-v1.mutation-plan.json",
    sha256 := "5489f223e2cf5362d718ca94935533cf2982beadd5c944b9c78e11cd54e89381" },
  { path := "qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json",
    sha256 := "478ad0be4fefe2f0e7e0e5cddc6b81171c5f0ed6f7fc32abc1d2156106781f15" },
  { path := "reference/single-group-correlation-v1.conformance.json",
    sha256 := "7e1b8f52ee08c8b3aed8e414df27573ebc9f8ffe27c4103aa8f954fe7277ec2d" }
] ++ postRevisionHistoricalArtifacts

private def frozenArtifactJson (artifact : FrozenArtifact) : Json :=
  Json.mkObj [("path", toJson artifact.path), ("sha256", toJson artifact.sha256)]

private def compatibilityJson (identity : CompatibilityIdentity) : Json :=
  Json.mkObj [
    ("referenceSemanticsVersion", toJson identity.referenceSemanticsVersion),
    ("protocolVersion", toJson identity.protocolVersion),
    ("manifestSchemaVersion", toJson identity.manifestSchemaVersion),
    ("kernelBehaviorVersion", toJson identity.kernelBehaviorVersion)]

private def capabilityJson (identity : CapabilityIdentity) : Json :=
  Json.mkObj [
    ("suiteId", toJson identity.suiteId),
    ("operation", toJson identity.operation)]

def historicalSeparatingReplayJson : Json :=
  Json.mkObj [
    ("receiptSchemaVersion", toJson 1),
    ("sourceRevision", toJson historicalReferenceRevision),
    ("compatibility", compatibilityJson historicalV0_2_0),
    ("capability", capabilityJson historicalFlatCapability),
    ("method", toJson "buildReferenceAtPinnedRevisionAndInvokeWithRetainedRequest"),
    ("request", Json.mkObj [
      ("path", toJson separatingRequest),
      ("sha256", toJson separatingRequestSha256)]),
    ("observedResponse", Json.mkObj [
      ("protocolVersion", toJson historicalV0_2_0.protocolVersion),
      ("kernelBehaviorVersion", toJson historicalV0_2_0.kernelBehaviorVersion),
      ("outcome", toJson "ok"),
      ("verdict", Json.mkObj [
        ("tag", toJson "fired"),
        ("polarity", toJson "omission")])])]

def currentSeparatingResponseJson : Json :=
  Json.mkObj [
    ("protocolVersion", toJson current.protocolVersion),
    ("kernelBehaviorVersion", toJson current.kernelBehaviorVersion),
    ("outcome", toJson "ok"),
    ("verdict", Json.mkObj [
      ("tag", toJson "fired"),
      ("polarity", toJson "value")])]

private def separatingObservationJson (polarity observationClass : String) : Json :=
  Json.mkObj [
    ("request", toJson separatingRequest),
    ("expectedVerdict", Json.mkObj [
      ("tag", toJson "fired"),
      ("polarity", toJson polarity)]),
    ("observationClass", toJson observationClass)]

def asJson : Json :=
  Json.mkObj [
    ("lineageSchemaVersion", toJson schemaVersion),
    ("lines", Json.arr #[
      Json.mkObj [
        ("compatibility", compatibilityJson historicalV0_2_0),
        ("capabilities", Json.arr #[
          capabilityJson historicalFlatCapability,
          capabilityJson historicalCorrelationCapability]),
        ("status", toJson "historical"),
        ("sourceRevision", toJson historicalReferenceRevision),
        ("supportManifest", toJson historicalSupportManifest),
        ("separatingObservation", separatingObservationJson "omission"
          "retainedProjectRevisionReplay"),
        ("artifactLock", frozenArtifactJson {
          path := historicalArtifactLock,
          sha256 := historicalArtifactLockSha256 }),
        ("separatingReplay", frozenArtifactJson historicalSeparatingReplay),
        ("frozenArtifacts", Json.arr
          (frozenHistoricalArtifacts.map frozenArtifactJson).toArray)],
      Json.mkObj [
        ("compatibility", compatibilityJson current),
        ("capabilities", Json.arr #[
          capabilityJson currentFlatCapability,
          capabilityJson currentCorrelationCapability]),
        ("status", toJson "current"),
        ("supportManifest", toJson currentSupportManifest),
        ("separatingObservation", separatingObservationJson "value"
          "currentProcessRegression")]])]

example : historicalReferenceSemanticsVersion != currentReferenceSemanticsVersion := by
  decide

example : current.kernelBehaviorVersion = A12Kernel.kernelVersion := by
  decide

/-- Line serialization is deliberately per-line: lineage remains well-defined when a future
protocol, manifest schema, or modeled-kernel version changes independently. -/
example :
    compatibilityJson
      { historicalV0_2_0 with protocolVersion := historicalV0_2_0.protocolVersion + 1 } !=
      compatibilityJson current := by
  native_decide

end A12Kernel.Reference.Lineage
