import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.ValidationMessageTypes

/-! # Running a DM model's rules over one document

Each rule is parsed, lowered at its declaring group and assembled with its error field, code and
severity; the checked rule then runs on the iteration plan its condition and error field certify. The
fired messages are projected to what a Kernel `validateFull` observation reports and this project
may compare: the error code, the error field's pointer and the message type. Rendered text is never
compared (CLAUDE.md, message catalog rule).

A scalar rule takes the full-validation content gate the once plan applies, the admitted content of
the error field's root instance. Lean's scalar rules otherwise receive that gate from their caller, so
this choice is the replay's and the population replay is what checks it.
-/

namespace A12Kernel.Dm

/-- A fired rule message as the Kernel reports it: code, pointer, `VALUE_ERROR` or
`OMISSION_ERROR`, and severity. -/
structure ObservedMessage where
  code : String
  pointer : String
  messageType : String
  severity : String
  deriving Repr, BEq, Ord, Inhabited

instance : ToString ObservedMessage where
  toString message := s!"{message.code}@{message.pointer}:{message.messageType}/{message.severity}"

/-- The message-parameter terminals a model's condition language selects. -/
def Language.messageKeywordProfile : Language → ValidationMessageKeywordProfile
  | .english => .english
  | .german => .german

def severity? : String → Option ValidationSeverity
  | "ERROR" => some .error
  | "WARNING" => some .warning
  | "INFO" => some .info
  | _ => none

/-- An error-target path read lexically from the rule element, one segment below `group`: each `..`
drops the last segment and each name appends one, so `..` may follow a name and `../../Order` from
`/Order` names `/Order` ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths)).
`none` for a path not starting with `..`, an empty segment, or one that climbs to or above the
document, which keep the ordinary path reading. -/
def lexicalErrorPath (group : GroupPath) (text : String) : Option GroupPath := do
  let segments := text.splitOn "/"
  if segments.head? != some ".." then none
  let path ← segments.foldlM (init := group ++ [""]) fun path segment =>
    if segment == ".." then (if path.isEmpty then none else some path.dropLast)
    else if segment.isEmpty then none else some (path ++ [segment])
  if path.isEmpty then none else pure path

/-- The entity an error-entity path names: a field, or else a declared group. The path is relative
to the rule element, so its first `..` climbs from the rule to the group declaring it, and it is
read lexically (`lexicalErrorPath`). A path naming neither keeps the field resolution's refusal.

A lexically read path names the model's own group and field names, which the walk judges and which
may hold a `.`, a `-` or a character the condition lexer has no terminal for beside its path class, so
it is resolved by segment and never lexed: a rule reporting on a field or group whose name holds such a
character draws no lexer class, unlike a computed field
([October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.13). Only
a path naming no declared entity meets the path grammar. -/
def errorEntityOf (language : Language) (model : FlatModel) (rule : DmRule) :
    Lowering RuleErrorEntity := do
  let lexical := lexicalErrorPath rule.group rule.errorEntityRelPath
  if let some named := lexical then
    if let some declaration := model.fields.find? (·.path == named) then return .field declaration.id
    if model.hasGroupPath named then return .group named
  let text := match lexical with
    | some path => "/" ++ "/".intercalate path
    | none => rule.errorEntityRelPath
  let path ← match parseModelPath language text with
    | .ok path => pure path
    | .error error => refuse "ErrorEntity" (repr error).pretty
  -- The path is written from the element, one step below its group; a relative path without that
  -- step is outside every retained model, so it is refused rather than read at the group.
  if !path.absolute && path.ups == 0 then refuse "ErrorEntity" rule.errorEntityRelPath
  let relative := if path.absolute then path else { path with ups := path.ups - 1 }
  let group? : Option GroupPath := relative.toGroupPath?.bind fun surface =>
    (SurfaceGroupPath.resolveAgainst surface rule.group).toOption.filter model.hasGroupPath
  -- A path of up-steps alone names a group, the rule's own included.
  let some field := relative.toFieldPath? | match group? with
    | some group => pure (.group group)
    | none => refuse "ErrorEntity" rule.errorEntityRelPath
  match model.resolveFieldDeclarationUnchecked rule.group field, group? with
  | .ok declaration, _ => pure (.field declaration.id)
  | .error _, some group => pure (.group group)
  | .error error, none => elaborated "ErrorEntity" (.error error)

/-- The field an error-entity path names, for a carrier that reports on fields only. -/
def errorFieldOf (language : Language) (model : FlatModel) (rule : DmRule) : Lowering FieldId := do
  match ← errorEntityOf language model rule with
  | .field field => pure field
  | .group _ => refuse "ErrorEntity" "group target outside the ordinary rule carrier"

/-- The group an error entity's static reads are judged from: a field's group, or the group itself. -/
def errorGroupOf (model : FlatModel) : RuleErrorEntity → Lowering GroupPath
  | .field field => do
      let declaration ← elaborated "ErrorEntity" (model.lookupUniqueId field)
      pure declaration.groupPath
  | .group path => pure path

/-- Apply the shared syntax and warning-suppression gates before choosing an execution carrier. -/
def parseValidationText (language : Language) (condition : String) : Lowering Text := do
  let text ← match parseText language condition with
    | .ok text => pure text
    | .error error => refuse "Syntax" error.errorClass.code
  if !text.body.parensLegal true then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
  -- The scale warning is the only suppressible one (spec §12.4); any other name is a static error.
  if text.suppressed.any (· != "MVK_INVALID_COMPARE_DEC_PLACES") then
    refuse "SuppressWarning" KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode
  pure text

/-- A rule-gate refusal's detail, the class the gate draws ahead of the cause. -/
def _root_.A12Kernel.FlatRuleAssemblyError.refusalDetail (error : FlatRuleAssemblyError) : String :=
  classifiedDetail error

/-- Parse, lower and assemble one rule, retaining named-type validity resolution from the supplied
world. Replay supplies the same registry used to prepare and evaluate the document. -/
private def checkRuleWith (useErrorBinding : Bool) (model : DmModel) (language : Language) (rule : DmRule)
    (world : World := { now := { epochMillis := 0 } }) :
    Lowering (CheckedResolvedValidationRule model.flat) := do
  admitDeclarations [rule.declaration]
  let text ← parseValidationText language rule.condition
  let suppress := text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES"
  -- Static reads use the error field's scope (spec/07 §3); that scope must not create runtime
  -- iteration for a fixed expression reporting below a star (ConstructedDateValidityLocks).
  let admissionGroup ← if useErrorBinding || text.body.needsOrderedAdmission then
      errorGroupOf model.flat (← errorEntityOf language model.flat rule)
    else pure rule.group
  let bindingGroup := if useErrorBinding || text.body.hasHaving then admissionGroup else rule.group
  checkOrderedAdmission model.flat rule.group admissionGroup text.body suppress
  let condition ← lowerCondition model.flat rule.group suppress text.body world bindingGroup
  let errorEntity ← errorEntityOf language model.flat rule
  let some severity := severity? rule.severity | refuse "Severity" rule.severity
  match assembleResolvedValidationRuleFor model.flat condition errorEntity rule.errorCode severity
      { parts := [] } with
  | .ok checked => pure checked
  | .error error => refuse "RuleAssembly" error.refusalDetail

/-- Ordered authored admission uses the error field's scope from the first attempt, including refused reads.
Other rules retain the compatibility fallback; lexical paths resolve at the declaring group. -/
def checkRule (model : DmModel) (language : Language) (rule : DmRule)
    (world : World := { now := { epochMillis := 0 } }) :
    Lowering (CheckedResolvedValidationRule model.flat) :=
  match checkRuleWith false model language rule world with
  | .ok checked => .ok checked
  | .error refusal =>
      match checkRuleWith true model language rule world with
      | .ok checked => .ok checked
      | .error boundRefusal =>
          -- A fully lowered row-bound tree reaches the rule gates; its refusal takes precedence
          -- over the lexical attempt's unbound read (H10 iteration-guard matrix). So does a bound
          -- refusal past the error field when the lexical one is a missing star: that level is the
          -- one the error field binds, so only the bound attempt judges the read as the Kernel does
          -- (spec/07 §3; SumOfProducts rows of inbound 2026-10-18, SPEC-2026-10-14-08). An error
          -- field that does not resolve binds nothing, so the lexical refusal stands.
          if boundRefusal.construct == "RuleAssembly" ||
              (refusal.kernelClass? == some KernelStaticDiagnostic.noWildcard.kernelCode &&
                boundRefusal.construct != "ErrorEntity") then
            .error boundRefusal
          else .error refusal

/-- The retained probe's message-address contract uses canonical text for exact pointers and its tool-owned fallback for partially known pointers (`KernelRuntimeProbe.address`, `A12Pointers.canonical`). A group entity renders its own path bare, its own first row included; a partially known one writes no coordinate for its own level, as the fallback writes none for a pointer's last segment (`formatPointer`). -/
def renderPointer (model : FlatModel) (pointer : RulePointer) : String :=
  match pointer.entity with
  | .group path => renderAt path []
  | .field field => match model.fields.find? (·.id == field) with
    | none => s!"#{field}"
    | some declaration => renderAt declaration.groupPath [declaration.name]
where
  renderAt (groupPath : GroupPath) (leaf : List String) : String :=
    let isPartial := pointer.coordinates.any fun coordinate => match coordinate with
      | .concrete _ => false
      | .wildcard | .unknown | .parallelIteration => true
    let rec walk (prefix_ : GroupPath) (remaining : List String)
        (coordinates : List MessageRepetitionCoordinate) : List String :=
      match remaining with
      | [] => []
      | name :: rest =>
          let path := prefix_ ++ [name]
          if isPartial && leaf.isEmpty && rest.isEmpty then [name]
          else if model.repeatableGroups.any (·.path == path) then
            let label := match coordinates.head? with
              | some (.concrete index) => if index == 1 && !isPartial then name else s!"{name}[{index}]"
              | some .wildcard => s!"{name}[0]"
              | some .unknown => s!"{name}[-5]"
              | some .parallelIteration => s!"{name}[-6]"
              | none => s!"{name}[?]"
            label :: walk path rest coordinates.tail
          else (if isPartial then s!"{name}[1]" else name) :: walk path rest coordinates
    (if isPartial then "/" else "") ++
      "/".intercalate (walk [] groupPath pointer.coordinates ++ leaf)

/-- A field pointer's canonical text, as a message's reference channels carry it. -/
def renderFieldPointer (model : FlatModel) (pointer : MessagePointer) : String :=
  renderPointer model pointer

def observe (model : FlatModel) (message : FlatRuleMessage) : ObservedMessage :=
  { code := message.errorCode, pointer := renderPointer model message.errorAddress
    messageType := match message.messageType with
      | .value => "VALUE_ERROR"
      | .omission => "OMISSION_ERROR"
    severity := match message.severity with
      | .error => "ERROR" | .warning => "WARNING" | .info => "INFO" }

/-- Run one checked rule over a checked document on its certified iteration plan, keeping the
environment each message fired at, which its reference channels are projected from. -/
def runRuleAt (world : World) (checked : CheckedDocument model)
    (rule : CheckedResolvedValidationRule model) (registry : CustomValidationRegistry model := {}) :
    Except String (List (Env × FlatRuleMessage)) :=
  match rule.ordinaryIterationPlan with
  | .rows _ =>
      match rule.evalOrdinaryRepeatableFull checked (some world) registry with
      | .ok rows => .ok (rows.filterMap fun (environment, outcome) => outcome.message?.map (environment, ·))
      | .error error => .error (repr error).pretty
  | .once _ =>
      match rule.evalOrdinaryOnceFull checked (some world) registry with
      | .ok (environment, outcome) => .ok (outcome.message?.toList.map (environment, ·))
      | .error error => .error (repr error).pretty
  | .scalar =>
      -- The scalar plan reads full validation's staged view too, as the row and once plans do
      -- (spec/10 §5).
      match checked.applyFullIndexPreliminary with
      | .error error => .error (repr error).pretty
      | .ok preliminary =>
          let checked := preliminary.defaultedInput
          let context : AddressedValidationEvaluationContext model := {
            scalar := {
              fields := checked.flatContext.withWorld world
              -- A fixed group operand reads its full-validation slice of the document, as the
              -- addressed numeric route does for the same groups. This context has no error channel, so
              -- an addressing error, which only a group below an unbound repeatable level could raise,
              -- reads as an unavailable group, UNKNOWN rather than a fault.
              groups := fun path =>
                (checked.groupPresenceInput path [] .fullyRelevant false).toOption.map (·.derive) }
            outer := []
            input := .checked checked }
          match rule.ordinaryOnceRootHasContent checked [] with
          | .error error => .error (repr error).pretty
          | .ok hasContent =>
              match rule.evalAddressedFull context hasContent registry with
              | .ok outcome => .ok (outcome.message?.toList.map ([], ·))
              | .error error => .error (repr error).pretty


/-- Run one checked rule over a checked document on its certified iteration plan. -/
def runRule (world : World) (checked : CheckedDocument model)
    (rule : CheckedResolvedValidationRule model) (registry : CustomValidationRegistry model := {}) :
    Except String (List FlatRuleMessage) :=
  (runRuleAt world checked rule registry).map (·.map (·.2))

end A12Kernel.Dm
