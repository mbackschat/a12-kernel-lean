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
  /-- A keyed value parameter's key selects no row, which faults the rule's evaluation; see
  `FlatRuleMessage.afterRendering` for the finding it reports. A keyed name or category does not fault. -/
  | unresolvedSelection
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

/-- A message reads an unbound level at its first row, whether or not that row exists, while a
duplicate or zero binding stays structural (rules `RS01`, `RS01C` on two documents). -/
private def messageCoordinate (context : ValidationMessageRowContext model compilePattern)
    (level : RepeatableLevel) : Except ValidationMessageRenderingError Nat :=
  match context.environment.bindingAt level with
  | .ok coordinate => pure coordinate
  | .error (.missingBinding _) => pure 1
  | .error error => throw (.environment error)

/-- The row a read reference renders. An unkeyed one reads the firing environment's binding of its own
levels, which a parallel caller extends with the joined partner row; a keyed one reads the row its key
selects through the shared message cache
([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15)).
Levels below the keyed group read like unkeyed ones. That is assumed, not measured: a keyed field of a
deeper group refuses its value statically and renders its name without a row. -/
def referencePath (context : ValidationMessageRowContext model compilePattern)
    (reference : CheckedValidationMessageReference model condition) :
    Except ValidationMessageRenderingError (List Nat) := do
  match reference.key with
  | none => reference.declaration.repeatableScope.mapM context.messageCoordinate
  | some key =>
      let some inputs := context.references | throw (.reference .missingIndexContext)
      let some group := model.semanticIndexGroupForPath? reference.declaration.groupPath
        | throw .invalidGroupBinding
      let some index := group.indexField | throw .invalidGroupBinding
      let some indexDeclaration := model.fields.find? (·.id == index) | throw .invalidGroupBinding
      match ← (inputs.resolveIndex group indexDeclaration key context.environment).mapError .reference with
      | (parent, .concrete row, _) =>
          let deeper := reference.declaration.repeatableScope.drop (parent.length + 1)
          pure (parent ++ [row] ++ (← deeper.mapM context.messageCoordinate))
      | _ => throw .unresolvedSelection

end ValidationMessageRowContext

/-- The environment a parallel firing renders its message at: both joined rows' bindings, so a read
of the partner group renders the joined row rather than the firing row's coordinate
([checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15), rule
`RPar`). The two sides share their outer frame, whose binding is kept once. A side the join leaves
missing binds nothing, so a read of it renders that level's first row as any unbound level does; that
is assumed, not measured, for a missing partner. -/
def ResolvedParallelIndexRow.messageEnvironment (row : ResolvedParallelIndexRow) : Env :=
  (row.left.environment.toList ++ row.right.environment.toList).foldl
    (fun bound side => bound ++ side.filter fun (level, _) => !bound.any (·.1 == level)) []

/-- Resolve message coordinates at the firing environment, then substitute opaque display text. -/
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
        fieldStoredToken := fun _ => token } (fun _ => 1) (fun _ => []))
  | .group access =>
      match access.key with
      | none =>
          let coordinate ← context.groupIndex access.group
          pure (part.toRenderPartWithGroupIndex inputs (fun _ => coordinate) (fun _ => []))
      | some key =>
          match ← context.selectedGroupIndex access.group key with
          | .concrete coordinate => pure (.group { repetitionIndex := coordinate })
          | .unknown => pure (.text "?")
          | .wildcard | .parallelIteration => throw .invalidGroupBinding
  | .fieldValue reference => do
      let path ← context.referencePath reference
      pure (part.toRenderPartWithGroupIndex inputs (fun _ => 1) (fun _ => path))
  | .fieldCategory access =>
      -- A key selecting no row renders an empty category rather than faulting (rule `RMissC`).
      match context.referencePath access.reference with
      | .ok path => pure (part.toRenderPartWithGroupIndex inputs (fun _ => 1) (fun _ => path))
      | .error .unresolvedSelection =>
          pure (part.toRenderPartWithGroupIndex { inputs with fieldStoredToken := fun _ => none }
            (fun _ => 1) (fun _ => []))
      | .error error => throw error
  | _ => pure (part.toRenderPartWithGroupIndex inputs (fun _ => 1) (fun _ => []))

def CheckedValidationMessageTemplate.toRenderPlanAt
    (template : CheckedValidationMessageTemplate model condition)
    (context : ValidationMessageRowContext model compilePattern)
    (inputs : ValidationMessageInputs) : Except ValidationMessageRenderingError MessageRenderPlan := do
  pure { parts := ← template.parts.mapM (·.toRenderPartAt context inputs) }

/-- A firing's finding once its template rendered at the firing row. A rendering fault is caught by the
generated rule's whole-rule handler, the one a runtime evaluation failure reaches
(MainValidatorController.addValidatorMessage): the finding keeps its code, address and severity, becomes
a value error, reports empty reference lists and carries the host's evaluation-fault text, which this
theory leaves empty (rules `RMiss`, `RMissK`, whose condition alone would report an omission error;
[checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15)).
Measured on a nonrepeatable error field only. Any other rendering error stays structural. -/
def FlatRuleMessage.afterRendering (message : FlatRuleMessage) :
    Except ValidationMessageRenderingError MessageRenderPlan →
      Except ValidationMessageRenderingError FlatRuleMessage
  | .ok plan => pure { message with text := plan.render }
  | .error .unresolvedSelection =>
      pure { message with origin := .runtimeFailure, messageType := .value, text := { text := "" } }
  | .error error => throw error

end A12Kernel
