import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.LowerValidation

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

/-- A fired rule message as the Kernel reports it: code, pointer and `VALUE_ERROR` or
`OMISSION_ERROR`. -/
structure ObservedMessage where
  code : String
  pointer : String
  messageType : String
  deriving Repr, BEq, Ord, Inhabited

instance : ToString ObservedMessage where
  toString message := s!"{message.code}@{message.pointer}:{message.messageType}"

private def severity? : String → Option ValidationSeverity
  | "ERROR" => some .error
  | "WARNING" => some .warning
  | "INFO" => some .info
  | _ => none

/-- The field an error-entity path names. The path is relative to the rule element, so its first
`..` climbs from the rule to the group declaring it. -/
def errorFieldOf (language : Language) (model : FlatModel) (rule : DmRule) : Lowering FieldId := do
  let text ← match parseText language rule.errorEntityRelPath with
    | .ok text => pure text
    | .error error => refuse "ErrorEntity" (repr error).pretty
  let some path := match text.body with
      | .entity { path, index := none, category := none } => some path
      | _ => none
    | refuse "ErrorEntity" rule.errorEntityRelPath
  -- The path is written from the element, one step below its group; a relative path without that
  -- step is outside every retained model, so it is refused rather than read at the group.
  if !path.absolute && path.ups == 0 then refuse "ErrorEntity" rule.errorEntityRelPath
  let relative := if path.absolute then path else { path with ups := path.ups - 1 }
  let some field := relative.toFieldPath? | refuse "ErrorEntity" rule.errorEntityRelPath
  let declaration ← elaborated "ErrorEntity" (model.resolveFieldDeclarationUnchecked rule.group field)
  pure declaration.id

/-- Parse, lower and assemble one rule. -/
def checkRule (model : DmModel) (language : Language) (rule : DmRule) :
    Lowering (CheckedResolvedValidationRule model.flat) := do
  let text ← match parseText language rule.condition with
    | .ok text => pure text
    | .error error => refuse "Syntax" error.errorClass.code
  let suppress := text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES"
  let condition ← lowerCondition model.flat rule.group suppress text.body
  let errorField ← errorFieldOf language model.flat rule
  let some severity := severity? rule.severity | refuse "Severity" rule.severity
  elaborated "RuleAssembly"
    (assembleResolvedValidationRule model.flat condition errorField rule.errorCode severity
      { parts := [] })

/-- The Kernel's text for a message pointer: the field's group path with each repeatable group's
index after it, written only when it is not `1`. -/
def renderPointer (model : FlatModel) (pointer : MessagePointer) : String :=
  match model.fields.find? (·.id == pointer.field) with
  | none => s!"#{pointer.field}"
  | some declaration =>
      let rec walk (prefix_ : GroupPath) (remaining : List String)
          (coordinates : List MessageRepetitionCoordinate) : List String :=
        match remaining with
        | [] => []
        | name :: rest =>
            let path := prefix_ ++ [name]
            if model.repeatableGroups.any (·.path == path) then
              let label := match coordinates.head? with
                | some (.concrete index) => if index == 1 then name else s!"{name}[{index}]"
                | some .wildcard => s!"{name}[*]"
                | _ => s!"{name}[?]"
              label :: walk path rest coordinates.tail
            else name :: walk path rest coordinates
      "/".intercalate (walk [] declaration.groupPath pointer.coordinates ++ [declaration.name])

def observe (model : FlatModel) (message : FlatRuleMessage) : ObservedMessage :=
  { code := message.errorCode, pointer := renderPointer model message.errorAddress
    messageType := match message.messageType with
      | .value => "VALUE_ERROR"
      | .omission => "OMISSION_ERROR" }

/-- Run one checked rule over a checked document on its certified iteration plan. -/
def runRule (world : World) (checked : CheckedDocument model)
    (rule : CheckedResolvedValidationRule model) : Except String (List FlatRuleMessage) :=
  match rule.ordinaryIterationPlan with
  | .rows _ =>
      match rule.evalOrdinaryRepeatableFull checked with
      | .ok rows => .ok (rows.filterMap (·.2.message?))
      | .error error => .error (repr error).pretty
  | .once _ =>
      match rule.evalOrdinaryOnceFull checked with
      | .ok (_, outcome) => .ok outcome.message?.toList
      | .error error => .error (repr error).pretty
  | .scalar =>
      let context : AddressedValidationEvaluationContext model := {
        scalar := {
          fields := checked.flatContext.withWorld world
          -- A fixed group operand reads its full-validation slice of the document, as the
          -- addressed numeric route does for the same groups.
          groups := fun path =>
            (checked.groupPresenceInput path [] .fullyRelevant false).toOption.map (·.derive) }
        outer := []
        input := .checked checked }
      match rule.ordinaryOnceRootHasContent checked [] with
      | .error error => .error (repr error).pretty
      | .ok hasContent =>
          match rule.evalAddressedFull context hasContent with
          | .ok outcome => .ok outcome.message?.toList
          | .error error => .error (repr error).pretty

end A12Kernel.Dm
