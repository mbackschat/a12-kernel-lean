import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel

/-- Inputs belonging to one firing row. The prepared checker owns conversion failures; the raw
document preserves category lookup independently of those failures (MainValidatorController.substIndexFieldRef). -/
structure ValidationMessageRowContext (model : FlatModel)
    (compilePattern : StringPatternCompiler) where
  environment : Env
  document : Document
  prepared : PreparedFlatStringContext model compilePattern
  locale : String
  displayEnumerations : Bool := true
  parallelIndexToken : Option String := none
  references : Option MessageReferenceInputs := none

inductive ValidationMessageRenderingError where
  | environment (error : EnvBindingError)
  | unsupportedIndexType
  | unsupportedDisplayLocale (locale : String)
  | reference (error : ReferenceProjectionError)
  | invalidGroupBinding
  deriving Repr, DecidableEq

namespace ValidationMessageRowContext

/-- Ordinary iteration reads the declared index address in the current parent; a parallel key
replaces that read. Missing input and present-empty index text both render empty. -/
def indexToken (context : ValidationMessageRowContext model compilePattern)
    (binding : MessageIndexBinding) : Except ValidationMessageRenderingError (Option String) := do
  let token ← match context.parallelIndexToken with
    | some token => pure (some token)
    | none => do
        let path ← (context.environment.pathForScope binding.declaration.repeatableScope).mapError .environment
        pure (context.document.rawCells { field := binding.declaration.id, path })
  pure (token.filter (!·.isEmpty))

/-- Reuse the declaration's formal checker before value conversion. Index substitution suppresses
failed conversion to empty, whereas category substitution only consults its stored-token map. -/
def indexDisplay (context : ValidationMessageRowContext model compilePattern)
    (binding : MessageIndexBinding) (token : String) :
    Except ValidationMessageRenderingError (Option String) := do
  let raw ← match binding.declaration.policy.kind with
    | .string => pure (RawCell.parsed (.str token))
    | .enumeration => pure (RawCell.parsed (.enum token))
    | _ => throw .unsupportedIndexType
  let checked := (context.prepared.checkContext context.locale {
    read := fun field => if field == binding.declaration.id then raw else .empty
  }).read binding.declaration.id
  if !checked.findings.isEmpty then return none
  match binding.declaration.enumeration with
  | none => pure (some token)
  | some source =>
      if !context.displayEnumerations || source.displayFacts.isEmpty then return some token
      if !source.displayFacts.any (·.locale == context.locale) then
        throw (.unsupportedDisplayLocale context.locale)
      pure ((source.displayFacts.find? (fun fact =>
        fact.locale == context.locale && fact.stored == token)).map (·.display))

def groupIndex (context : ValidationMessageRowContext model compilePattern)
    (group : GroupPath) : Except ValidationMessageRenderingError Nat :=
  match model.repeatableGroups.find? (·.path == group) with
  | some declaration =>
      if declaration.repeatability.any (· > 1) then
        (context.environment.bindingAt declaration.level).mapError .environment
      else pure 1
  | none => pure 1

def selectedGroupIndex (context : ValidationMessageRowContext model compilePattern)
    (group : GroupPath) (key : CheckedSemanticIndexKey) :
    Except ValidationMessageRenderingError MessageRepetitionCoordinate := do
  let some inputs := context.references | throw (.reference .missingIndexContext)
  let some declaration := model.repeatableGroups.find? (·.path == group)
    | throw .invalidGroupBinding
  let some index := declaration.indexField | throw .invalidGroupBinding
  let some indexDeclaration := model.fields.find? (·.id == index) | throw .invalidGroupBinding
  let (_, coordinate, _) ← (inputs.resolveIndex declaration indexDeclaration key context.environment).mapError .reference
  pure coordinate

end ValidationMessageRowContext

/-- Resolve message coordinates at the firing environment, then substitute opaque display text.
Missing row bindings are structural failures, never invented row 1 coordinates. -/
def CheckedValidationMessagePart.toRenderPartAt
    (part : CheckedValidationMessagePart model condition)
    (context : ValidationMessageRowContext model compilePattern)
    (inputs : ValidationMessageInputs) : Except ValidationMessageRenderingError MessageRenderPart := do
  match part with
  | .indexField access =>
      let token ← context.indexToken access.binding
      let display ← match access.suffix, token with
        | .value, some token => context.indexDisplay access.binding token
        | _, _ => pure none
      pure (part.toRenderPartWithGroupIndex { inputs with
        fieldValue := fun _ => { displayValue := display, defaultDisplay := "" }
        fieldStoredToken := fun _ => token } (fun _ => 1))
  | .group access =>
      match access.key with
      | none =>
          let coordinate ← context.groupIndex access.group
          pure (part.toRenderPartWithGroupIndex inputs (fun _ => coordinate))
      | some key =>
          match ← context.selectedGroupIndex access.group key with
          | .concrete coordinate => pure (.group { repetitionIndex := coordinate })
          | .unknown => pure (.text "?")
          | .wildcard => throw .invalidGroupBinding
  | _ => pure (part.toRenderPartWithGroupIndex inputs (fun _ => 1))

def CheckedValidationMessageTemplate.toRenderPlanAt
    (template : CheckedValidationMessageTemplate model condition)
    (context : ValidationMessageRowContext model compilePattern)
    (inputs : ValidationMessageInputs) : Except ValidationMessageRenderingError MessageRenderPlan := do
  pure { parts := ← template.parts.mapM (·.toRenderPartAt context inputs) }

end A12Kernel
