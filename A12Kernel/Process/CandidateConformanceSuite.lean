import Lean.Data.Json

/-! # Candidate-conformance suite vocabulary

This module owns the decoded suite and evidence-link vocabulary used by the bounded candidate runner. It contains no process execution, fixture loading, or semantic evaluation.
-/

namespace A12Kernel.CandidateConformance

/-- External evidence class attached to one finite conformance case. -/
inductive EvidenceKind where
  | kernelRuntimeObservation
  | kernelStaticDiagnostic
  | kernelStaticAcceptance
  deriving Repr, DecidableEq

namespace EvidenceKind

def tag : EvidenceKind → String
  | .kernelRuntimeObservation => "kernelRuntimeObservation"
  | .kernelStaticDiagnostic => "kernelStaticDiagnostic"
  | .kernelStaticAcceptance => "kernelStaticAcceptance"

def fromTag? : String → Option EvidenceKind
  | "kernelRuntimeObservation" => some .kernelRuntimeObservation
  | "kernelStaticDiagnostic" => some .kernelStaticDiagnostic
  | "kernelStaticAcceptance" => some .kernelStaticAcceptance
  | _ => none

end EvidenceKind

/-- Exact observation fidelity supplied by one evidence link. -/
inductive ExternalSupport where
  | firingRows
  | verdictFiringAndPolarity
  | verdictSuppressionOnly
  | elaborationRejectionClass
  | elaborationAcceptanceOnly
  deriving Repr, DecidableEq

namespace ExternalSupport

def tag : ExternalSupport → String
  | .firingRows => "firingRows"
  | .verdictFiringAndPolarity => "verdictFiringAndPolarity"
  | .verdictSuppressionOnly => "verdictSuppressionOnly"
  | .elaborationRejectionClass => "elaborationRejectionClass"
  | .elaborationAcceptanceOnly => "elaborationAcceptanceOnly"

def fromTag? : String → Option ExternalSupport
  | "firingRows" => some .firingRows
  | "verdictFiringAndPolarity" => some .verdictFiringAndPolarity
  | "verdictSuppressionOnly" => some .verdictSuppressionOnly
  | "elaborationRejectionClass" => some .elaborationRejectionClass
  | "elaborationAcceptanceOnly" => some .elaborationAcceptanceOnly
  | _ => none

end ExternalSupport

/-- Provenance class for the exact expected response bytes. -/
inductive ExpectedResponseSource where
  | retainedProjection
  | projectDiagnostic
  | leanRuntimeProjection
  deriving Repr, DecidableEq

namespace ExpectedResponseSource

def tag : ExpectedResponseSource → String
  | .retainedProjection => "retainedProjection"
  | .projectDiagnostic => "projectDiagnostic"
  | .leanRuntimeProjection => "leanRuntimeProjection"

def fromTag? : String → Option ExpectedResponseSource
  | "retainedProjection" => some .retainedProjection
  | "projectDiagnostic" => some .projectDiagnostic
  | "leanRuntimeProjection" => some .leanRuntimeProjection
  | _ => none

end ExpectedResponseSource

/-- Evidence identity and fidelity retained by one suite case. -/
structure EvidenceLink where
  kind : EvidenceKind
  projection : System.FilePath
  caseId : String
  externalSupports : ExternalSupport
  expectedResponseSource : ExpectedResponseSource

/-- One normalized request/response case and its exact evidence boundary. -/
structure ConformanceCase where
  id : String
  request : System.FilePath
  expectedResponse : System.FilePath
  evidence : EvidenceLink
  covers : List String

/-- Closed candidate-suite metadata consumed before any process is invoked. -/
structure ConformanceSuite where
  id : String
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  operation : String
  supportManifest : System.FilePath
  cases : List ConformanceCase

end A12Kernel.CandidateConformance
