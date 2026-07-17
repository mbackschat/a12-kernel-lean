import A12Kernel.Basic
import A12Kernel.Evidence.StringCascadeSchema
import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Evidence.StringCascadeReplay — observable direct-cascade replay

The retained request is input-only. This module closes that five-case input matrix, evaluates the existing two-step Lean account, and projects only externally observable clean results, target errors, deltas, and value-only applied states. It does not claim that the packet directly exposes the internal dependency cell, poison tag, or scheduling mechanism.
-/

namespace A12Kernel.Evidence.StringCascade

open A12Kernel

private def sourcePath := "/Cascade/Source"
private def midPath := "/Cascade/Mid"
private def outPath := "/Cascade/Out"
private def midPointer := "/Cascade[1]/Mid"
private def outPointer := "/Cascade[1]/Out"
private def midComputation := "/Cascade/MidComputation"
private def outComputation := "/Cascade/OutComputation"

private def groupPlacement : Placement := {
  kind := "GROUP"
  path := "/Cascade"
  reps := [1]
  value := none }

private def fieldPlacement (path value : String) : Placement := {
  kind := "FIELD"
  path
  reps := [1, 1]
  value := some value }

private def scenarioCase (id : String) (source mid : Option String) : ScenarioCase := {
  caseId := id
  modelRef := "models/string-direct-cascade.json"
  operation := "compute"
  placements :=
    [groupPlacement] ++
    (source.map (fieldPlacement sourcePath)).toList ++
    (mid.map (fieldPlacement midPath)).toList ++
    [fieldPlacement outPath "STALE"]
  probes := [midPointer, outPointer] }

namespace ScenarioRequest

def expected : ScenarioRequest := {
  scenarioId := "string-direct-cascade-v1"
  scenarioVersion := "1"
  operationSchema := "compute-observation-v1"
  capabilitiesSchema := "a12-dmkits-capture-capabilities-v1"
  capabilitiesVersion := "1"
  worldProfile := "local-wallclock-v1"
  locale := "en_US"
  modelRef := "models/string-direct-cascade.json"
  modelSha256 := "3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d"
  requiredRunners := [
    "kernel-groovy-dynamic",
    "kernel-java-static",
    "a12-dmkits-interpreter"]
  qualificationPolicy := "kernel-route-confirmed-v1"
  observationRequirementId := "string-direct-cascade-kernel-route-v1"
  observationRequirementVersion := "1"
  requiredChannels := [
    "withoutErrors",
    "changedSubset",
    "withErrors",
    "cleared",
    "formalErrorsInOperands",
    "appliedState"]
  comparisonProjections := [
    "compute-projection-kernel-route-v1",
    "compute-projection-dmkits-portable-v1"]
  cases := [
    scenarioCase "source-abc-mid-old" (some "ABC") (some "OLD"),
    scenarioCase "source-abc-mid-abc" (some "ABC") (some "ABC"),
    scenarioCase "source-absent-mid-old" none (some "OLD"),
    scenarioCase "source-absent-mid-absent" none none,
    scenarioCase "source-abcd-mid-old" (some "ABCD") (some "OLD")] }

def validate (request : ScenarioRequest) : Except String Unit := do
  if request != expected then
    throw "direct-cascade scenario request differs from the closed input-only matrix"

end ScenarioRequest

structure CaseInput where
  source : Option String
  priorMid : Option String
  priorOut : String
  deriving Repr, DecidableEq

namespace ScenarioCase

private def fieldValue (case : ScenarioCase) (path : String) : Except String (Option String) :=
  match case.placements.filter (fun placement =>
      placement.kind == "FIELD" && placement.path == path) with
  | [] => pure none
  | [placement] => pure placement.value
  | _ => throw s!"{case.caseId}: duplicate field placement for '{path}'"

def toInput (case : ScenarioCase) : Except String CaseInput := do
  let source ← case.fieldValue sourcePath
  let priorMid ← case.fieldValue midPath
  let priorOut ← case.fieldValue outPath
  let priorOut ← match priorOut with
    | some value => pure value
    | none => throw s!"{case.caseId}: missing prior Out placement"
  pure { source, priorMid, priorOut }

end ScenarioCase

structure ValueResult where
  target : String
  computation : String
  value : String
  deriving Repr, DecidableEq

structure ErrorResult where
  target : String
  computation : String
  attempted : String
  code : String
  messageType : String
  errorPointer : String
  deriving Repr, DecidableEq

structure AppliedValueResult where
  pointer : String
  value : Option String
  deriving Repr, DecidableEq

structure CoreProjection where
  clean : List ValueResult
  changed : List ValueResult
  errors : List ErrorResult
  cleared : List (String × String)
  applied : List AppliedValueResult
  deriving Repr, DecidableEq

private def optionalValueSignature : Option String → String
  | none => "no-value"
  | some value => s!"value|{value}"

namespace CoreProjection

private def valueSignature (kind : String) (entry : ValueResult) : String :=
  s!"{kind}|{entry.target}|{entry.value}"

private def errorSignature (entry : ErrorResult) : String :=
  s!"error|{entry.target}|{entry.attempted}|{entry.code}|{entry.messageType}|{entry.errorPointer}"

private def appliedSignature (entry : AppliedValueResult) : String :=
  s!"applied|{entry.pointer}|{optionalValueSignature entry.value}"

def signatures (projection : CoreProjection) : List String :=
  (projection.clean.map (valueSignature "clean") ++
    projection.changed.map (valueSignature "changed") ++
    projection.errors.map errorSignature ++
    projection.cleared.map (fun entry => s!"cleared|{entry.1}") ++
    projection.applied.map appliedSignature).mergeSort

end CoreProjection

private def checkedString : Option String → CheckedCell
  | none => formalCheck { kind := .string } .empty
  | some value => formalCheck { kind := .string } (.parsed (.str value))

private def computationContext (input : CaseInput) : StringComputationContext where
  read field :=
    if field == 1 then checkedString input.source
    else if field == 2 then checkedString input.priorMid
    else checkedString none

private def stored (context value : String) : Except String StoredString :=
  if nonempty : value ≠ "" then
    pure { text := value, nonempty }
  else
    throw s!"{context}: a prior stored String cannot be empty"

private def prior (context : String) : Option String → Except String PriorStringTarget
  | none => pure .empty
  | some value => .filled <$> stored context value

private def cascade (input : CaseInput) : Except String StringDirectCascade := do
  let midPrior ← prior "prior Mid" input.priorMid
  let outPrior ← prior "prior Out" (some input.priorOut)
  pure {
    producer := {
      targetField := 2
      expression := .field 1
      targetPolicy := .maximum { value := 3, positive := by decide }
      prior := midPrior }
    consumer := {
      targetField := 3
      expression := .concat (.field 2) (.literal "-X")
      targetPolicy := .unconstrained
      prior := outPrior } }

private def acceptedResult (target computation : String) :
    StringTargetOutcome → List ValueResult
  | .accepted value => [{ target, computation, value := value.text }]
  | _ => []

private def changedResult (target computation : String) :
    Option StringDelta → List ValueResult
  | some (.value value) => [{ target, computation, value := value.text }]
  | _ => []

private def clearedResult (target computation : String) :
    Option StringDelta → List (String × String)
  | some .cleared => [(target, computation)]
  | _ => []

private def errorResult (target computation : String) :
    StringTargetOutcome → List ErrorResult
  | .errored attempted cause => [{
      target
      computation
      attempted := attempted.text
      code := match cause with
        | .tooShort => "stringZuKurz"
        | .tooLong => "stringZuLang"
      messageType := "VALUE_ERROR"
      errorPointer := target }]
  | _ => []

private def appliedResult (pointer : String)
    (outcome : StringTargetOutcome) : AppliedValueResult := {
  pointer
  value := outcome.appliedValue.map (·.text) }

def ScenarioCase.replay (case : ScenarioCase) : Except String CoreProjection := do
  let input ← case.toInput
  let cascade ← cascade input
  let result ← match cascade.evaluate (computationContext input) with
    | .ok result => pure result
    | .error fault => throw s!"{case.caseId}: direct cascade left the admitted fragment: {repr fault}"
  pure {
    clean :=
      acceptedResult midPointer midComputation result.producer.outcome ++
      acceptedResult outPointer outComputation result.consumer.outcome
    changed :=
      changedResult midPointer midComputation result.producer.delta ++
      changedResult outPointer outComputation result.consumer.delta
    errors :=
      errorResult midPointer midComputation result.producer.outcome ++
      errorResult outPointer outComputation result.consumer.outcome
    cleared :=
      clearedResult midPointer midComputation result.producer.delta ++
      clearedResult outPointer outComputation result.consumer.delta
    applied := [
      appliedResult midPointer result.producer.outcome,
      appliedResult outPointer result.consumer.outcome] }

private def kernelText (context : String) (value : TransportValue) : Except String String :=
  match value.typed.availability, value.typed.kind, value.typed.value,
      value.rendered.availability, value.rendered.kind, value.rendered.value with
  | .available, some "STRING", some typed,
      .available, none, some rendered =>
      if typed == rendered then pure typed
      else throw s!"{context}: typed and rendered values disagree"
  | _, _, _, _, _, _ =>
      throw s!"{context}: kernel projection requires typed and rendered String values"

private def validateTarget (context target computation : String) : Except String Unit :=
  if (target == midPointer && computation == midComputation) ||
      (target == outPointer && computation == outComputation) then
    pure ()
  else
    throw s!"{context}: target and declared computation do not form a known pair"

private def projectValue (context : String) (entry : CleanEntry) : Except String ValueResult := do
  validateTarget context entry.target entry.declaredComputation
  pure {
    target := entry.target
    computation := entry.declaredComputation
    value := ← kernelText (context ++ ".value") entry.value }

private def projectError (context : String) (entry : ErrorEntry) : Except String ErrorResult := do
  validateTarget context entry.target entry.declaredComputation
  let attempted ← kernelText (context ++ ".attempted") entry.attempted
  let code ← match entry.cause.code with
    | some code => pure code
    | none => throw s!"{context}: kernel error cause has no code"
  let messageType ← match entry.cause.messageType with
    | some messageType => pure messageType
    | none => throw s!"{context}: kernel error cause has no message type"
  let errorPointer ← match entry.cause.errorPointer with
    | some pointer => pure pointer
    | none => throw s!"{context}: kernel error cause has no pointer"
  if entry.cause.availability != .available then
    throw s!"{context}: kernel error cause is unavailable"
  pure {
    target := entry.target
    computation := entry.declaredComputation
    attempted
    code
    messageType
    errorPointer }

private def projectCleared (context : String)
    (entry : ClearedEntry) : Except String (String × String) := do
  validateTarget context entry.target entry.declaredComputation
  pure (entry.target, entry.declaredComputation)

private def projectApplied (context : String)
    (entry : AppliedEntry) : Except String AppliedValueResult := do
  if entry.pointer != midPointer && entry.pointer != outPointer then
    throw s!"{context}: unknown applied-state probe '{entry.pointer}'"
  let value ← match entry.state with
    | .absent | .presentEmpty => pure none
    | .presentValue value =>
        match value.typed.availability, value.typed.kind, value.typed.value,
            value.rendered.availability, value.rendered.kind, value.rendered.value with
        | .available, some "STRING", some typed,
            .notExposedByRunner, none, none => pure (some typed)
        | .available, some "STRING", some typed,
            .available, none, some rendered =>
            if typed == rendered then pure (some typed)
            else throw s!"{context}.value: typed and rendered applied values disagree"
        | _, _, _, _, _, _ =>
            throw s!"{context}.value: kernel applied state requires an available typed String"
    | .noValueIndeterminate =>
        throw s!"{context}: a kernel route cannot report an indeterminate no-value state"
  pure { pointer := entry.pointer, value }

private def requireKernelChannel (context : String) (channel : Channel α)
    (granularity : String) : Except String Unit := do
  if channel.availability != .available || channel.granularity != granularity ||
      channel.order != "observed" then
    throw s!"{context}: kernel channel fidelity differs from the declared profile"

def Observation.projectKernel (observation : Observation) : Except String CoreProjection := do
  if observation.runner != "kernel-groovy-dynamic" &&
      observation.runner != "kernel-java-static" then
    throw s!"{observation.caseId}: '{observation.runner}' is not a kernel route"
  if observation.status != "success" || observation.statusDetail.isSome then
    throw s!"{observation.caseId}: kernel observation did not complete successfully"
  requireKernelChannel "withoutErrors" observation.withoutErrors "all-computed-clean"
  requireKernelChannel "changedSubset" observation.changedSubset "delta-vs-input"
  requireKernelChannel "withErrors" observation.withErrors "errored-instances"
  requireKernelChannel "cleared" observation.cleared "input-filled-only"
  requireKernelChannel "formalErrorsInOperands" observation.formalErrorsInOperands
    "operand-formal-errors"
  requireKernelChannel "appliedState" observation.appliedState "requested-probes"
  if !observation.formalErrorsInOperands.entries.isEmpty then
    throw s!"{observation.caseId}: direct-cascade kernel observation has operand formal errors"
  pure {
    clean := ← observation.withoutErrors.entries.zipIdx.mapM fun (entry, index) =>
      projectValue s!"withoutErrors[{index}]" entry
    changed := ← observation.changedSubset.entries.zipIdx.mapM fun (entry, index) =>
      projectValue s!"changedSubset[{index}]" entry
    errors := ← observation.withErrors.entries.zipIdx.mapM fun (entry, index) =>
      projectError s!"withErrors[{index}]" entry
    cleared := ← observation.cleared.entries.zipIdx.mapM fun (entry, index) =>
      projectCleared s!"cleared[{index}]" entry
    applied := ← observation.appliedState.entries.zipIdx.mapM fun (entry, index) =>
      projectApplied s!"appliedState[{index}]" entry }

structure PortableProjection where
  clean : List (String × String)
  errors : List (String × String)
  cleared : List String
  applied : List (String × Option String)
  deriving Repr, DecidableEq

namespace PortableProjection

def signatures (projection : PortableProjection) : List String :=
  (projection.clean.map (fun entry => s!"clean|{entry.1}|{entry.2}") ++
    projection.errors.map (fun entry => s!"error|{entry.1}|{entry.2}") ++
    projection.cleared.map (fun target => s!"cleared|{target}") ++
    projection.applied.map (fun entry =>
      s!"applied|{entry.1}|{optionalValueSignature entry.2}")).mergeSort

end PortableProjection

private def portableText (context : String) (value : TransportValue) : Except String String :=
  match value.text? with
  | some text => pure text
  | none => throw s!"{context}: neither typed nor rendered value is exposed"

private def ScenarioCase.hasInputTarget (case : ScenarioCase) (target : String) : Bool :=
  let path :=
    if target == midPointer then midPath
    else if target == outPointer then outPath
    else ""
  !path.isEmpty && case.placements.any fun placement =>
    placement.kind == "FIELD" && placement.path == path

private def requireInterpreterChannel (context : String) (channel : Channel α)
    (availability : Availability) (granularity order : String) : Except String Unit := do
  if channel.availability != availability || channel.granularity != granularity ||
      channel.order != order then
    throw s!"{context}: interpreter channel fidelity differs from the frozen V1 declaration"

private def requireInterpreterValue (context : String)
    (value : TransportValue) : Except String Unit := do
  if value.typed.availability != .notExposedByRunner ||
      value.typed.kind.isSome || value.typed.value.isSome then
    throw s!"{context}: interpreter typed value fidelity differs from the frozen V1 declaration"
  if value.rendered.availability != .available ||
      value.rendered.kind.isSome || value.rendered.value.isNone then
    throw s!"{context}: interpreter rendered value fidelity differs from the frozen V1 declaration"

private def requireInterpreterCause (context : String)
    (cause : ErrorCause) : Except String Unit := do
  if cause.availability != .notExposedByRunner ||
      cause.code.isSome || cause.messageType.isSome || cause.errorPointer.isSome then
    throw s!"{context}: interpreter error cause fidelity differs from the frozen V1 declaration"

private def requireInterpreterAppliedState (context : String)
    (entry : AppliedEntry) : Except String Unit := do
  match entry.state with
  | .noValueIndeterminate => pure ()
  | .presentValue value => requireInterpreterValue (context ++ ".value") value
  | .absent | .presentEmpty =>
      throw s!"{context}: interpreter no-value state exposes a distinction unavailable in frozen V1"

def Observation.projectPortable (case : ScenarioCase) (observation : Observation) :
    Except String PortableProjection := do
  if observation.status != "success" || observation.statusDetail.isSome then
    throw s!"{observation.caseId}: observation did not complete successfully"
  if observation.runner == "a12-dmkits-interpreter" then
    requireInterpreterChannel "withoutErrors" observation.withoutErrors
      .available "all-computed-clean" "observed"
    requireInterpreterChannel "changedSubset" observation.changedSubset
      .notExposedByRunner "notExposed" "notApplicable"
    requireInterpreterChannel "withErrors" observation.withErrors
      .available "errored-instances" "observed"
    requireInterpreterChannel "cleared" observation.cleared
      .available "all-cleared" "observed"
    requireInterpreterChannel "formalErrorsInOperands" observation.formalErrorsInOperands
      .notExposedByRunner "notExposed" "notApplicable"
    requireInterpreterChannel "appliedState" observation.appliedState
      .available "requested-probes" "observed"
    for entry in observation.withoutErrors.entries do
      requireInterpreterValue "withoutErrors.value" entry.value
    for entry in observation.withErrors.entries do
      requireInterpreterValue "withErrors.attempted" entry.attempted
      requireInterpreterCause "withErrors.cause" entry.cause
    for entry in observation.appliedState.entries do
      requireInterpreterAppliedState "appliedState" entry
  else
    discard <| observation.projectKernel
  let clean ← observation.withoutErrors.entries.zipIdx.mapM fun (entry, index) => do
    validateTarget s!"portable withoutErrors[{index}]" entry.target entry.declaredComputation
    pure (entry.target, ← portableText s!"portable withoutErrors[{index}]" entry.value)
  let errors ← observation.withErrors.entries.zipIdx.mapM fun (entry, index) => do
    validateTarget s!"portable withErrors[{index}]" entry.target entry.declaredComputation
    pure (entry.target, ← portableText s!"portable withErrors[{index}]" entry.attempted)
  let cleared ← observation.cleared.entries.zipIdx.mapM fun (entry, index) => do
    validateTarget s!"portable cleared[{index}]" entry.target entry.declaredComputation
    pure entry.target
  let applied ← observation.appliedState.entries.zipIdx.mapM fun (entry, index) => do
    if entry.pointer != midPointer && entry.pointer != outPointer then
      throw s!"portable appliedState[{index}]: unknown probe '{entry.pointer}'"
    let value ← match entry.state with
      | .absent | .presentEmpty | .noValueIndeterminate => pure none
      | .presentValue value =>
          some <$> portableText s!"portable appliedState[{index}]" value
    pure (entry.pointer, value)
  pure {
    clean
    errors
    cleared := cleared.filter case.hasInputTarget
    applied }

end A12Kernel.Evidence.StringCascade
