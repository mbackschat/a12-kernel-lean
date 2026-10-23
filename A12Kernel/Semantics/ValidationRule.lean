import A12Kernel.Semantics.PartialValidation
import A12Kernel.Semantics.MessagePointer
import A12Kernel.Semantics.GroupReference

/-! # One flat validation-rule emission boundary

This capsule attaches whole-rule metadata to the existing flat condition verdict. Its low-level input assumes an already-lowered condition, resolved error entity, nonrepeatable context, and parser-independent structured message plan. The plan's provider/default selection and one-pass rendering occur only after the condition fires. Authored-template parsing and legality, field lookup, provider invocation, locale and display conversion, repeatable addressing, partial validation, rule collections, and orchestration remain outside.
-/

namespace A12Kernel

/-- Message severity is metadata and never an input to condition evaluation. -/
inductive ValidationSeverity where
  | error
  | warning
  | info
  deriving Repr, DecidableEq

/-- End-user text after any interpolation. The nominal wrapper prevents this capsule from mistaking resolved bytes for an authored template. -/
structure ResolvedMessageText where
  text : String
  deriving Repr, DecidableEq

/-- Inputs needed after a field-name token has already resolved to one field instance. A provider result, including an empty result, wins; otherwise a nonempty model label precedes the caller's debug representation. Locale selection and provider invocation happen before this boundary. -/
structure MessageNameInput where
  providerResult : Option String
  modelLabel : Option String
  debugDisplay : String
  deriving Repr, DecidableEq

namespace MessageNameInput

def resolve (input : MessageNameInput) : String :=
  match input.providerResult with
  | some label => label
  | none =>
      match input.modelLabel with
      | some label => if label.isEmpty then input.debugDisplay else label
      | none => input.debugDisplay

end MessageNameInput

/-- Display-layer input for one field-value token. The caller supplies the field format's exact default, so this renderer does not invent Number scale, locale, date, Boolean, enumeration, or unit formatting. A missing or empty display value selects that default. -/
structure MessageValueInput where
  displayValue : Option String
  defaultDisplay : String
  deriving Repr, DecidableEq

namespace MessageValueInput

def resolve (input : MessageValueInput) : String :=
  match input.displayValue with
  | some value => if value.isEmpty then input.defaultDisplay else value
  | none => input.defaultDisplay

end MessageValueInput

/-- One Enumeration category access, already resolved to the category token the field's current
stored value maps to. `none` is an empty field or a value the category does not map; both render as
the empty string, which is the measured behaviour only for a mapped value — the absent case is this
project's default and carries no observation. -/
structure MessageCategoryInput where
  categoryToken : Option String
  deriving Repr, DecidableEq

/-- One admitted group-position parameter, already resolved to the group it names, carrying what the
Kernel renders for it: the **1-based repetition index** of that group in the firing row, and `1` for a
nonrepeatable group ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index)).
The index is the row's own, not a firing ordinal — a rule firing on rows 2 and 3 renders `2` and `3`.

The flat authoring route supplies `1`; the addressed message renderer supplies the named level's
coordinate or its semantic-index cache selection. An unknown selected coordinate is rendered as
text by that caller, rather than coerced into a natural-number coordinate. -/
structure MessageGroupInput where
  repetitionIndex : Nat
  deriving Repr, DecidableEq

/-- One form-pointer parameter, the Kernel's `Vordruckzeile` and `Vordruckname` terminals applied to a
field. What either **renders** is unmeasured, so the bytes are caller-supplied exactly as a name or a
value input's are. It keeps its own record rather than folding into `text` because the two are not
interchangeable to a reader of the plan: a form pointer is a resolved parameter position, and an
Explain consumer that cannot tell it from authored text loses the parameter. -/
structure MessageFormPointerInput where
  text : String
  deriving Repr, DecidableEq

/-- One already-decoded rule-message part. Field references and `$` syntax have been checked before this point; replacement strings are opaque and are never parsed again. -/
inductive MessageRenderPart where
  | text (value : String)
  | fieldName (input : MessageNameInput)
  | fieldValue (input : MessageValueInput)
  | fieldCategory (input : MessageCategoryInput)
  /-- The model's Base Year with the parameter's authored offset already applied. It carries no input
  record because nothing about it depends on the document or on a provider. -/
  | baseYear (year : Int)
  /-- A group-position parameter, which renders the firing row's coordinate for the named group. -/
  | group (input : MessageGroupInput)
  /-- A form-pointer parameter, whose rendered text stays caller-supplied while it is unmeasured. -/
  | formPointer (input : MessageFormPointerInput)
  deriving Repr, DecidableEq

namespace MessageRenderPart

def render : MessageRenderPart → String
  | .text value => value
  | .fieldName input => input.resolve
  | .fieldValue input => input.resolve
  | .fieldCategory input => input.categoryToken.getD ""
  | .baseYear year => toString year
  | .group input => toString input.repetitionIndex
  | .formPointer input => input.text

end MessageRenderPart

/-- Ordered, structured input to the resolved-message renderer. This is not raw authored `$...$` syntax. A decoded literal dollar is ordinary text. -/
structure MessageRenderPlan where
  parts : List MessageRenderPart
  deriving Repr, DecidableEq

namespace MessageRenderPlan

def renderText : List MessageRenderPart → String
  | [] => ""
  | part :: rest => part.render ++ renderText rest

/-- Render each structured part exactly once, from left to right. -/
def render (plan : MessageRenderPlan) : ResolvedMessageText :=
  { text := renderText plan.parts }

end MessageRenderPlan

/-- The entity a rule reports on. A rule may name a group as well as a field; its message then
points at the group itself, at its first row when the group repeats
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join)). -/
inductive RuleErrorEntity where
  | field (id : FieldId)
  | group (path : GroupPath)
  deriving Repr, DecidableEq

/-- A fired rule message's address: its error entity with the repetition coordinates of every
repeatable level the entity's path carries, its own level included for a repeating group. -/
structure RulePointer where
  entity : RuleErrorEntity
  coordinates : List MessageRepetitionCoordinate
  deriving Repr, DecidableEq

/-- A field pointer is the field-entity rule pointer, so every formal-message channel's field
address is also a rule address. -/
instance : Coe MessagePointer RulePointer where
  coe pointer := { entity := .field pointer.field, coordinates := pointer.coordinates }

namespace RulePointer

/-- The field pointer of a field entity; a group entity has none. -/
def field? (pointer : RulePointer) : Option MessagePointer :=
  match pointer.entity with
  | .field field => some { field, coordinates := pointer.coordinates }
  | .group _ => none

/-- Recover an exact document address for a field entity whose coordinates are all concrete. -/
def toCellAddr? (pointer : RulePointer) : Option CellAddr :=
  pointer.field?.bind MessagePointer.toCellAddr?

end RulePointer

/-- One already-resolved rule instance, parametric only in its condition representation. Message display inputs remain structured until a fired verdict reaches the renderer. -/
structure ResolvedRule (Condition : Type) where
  condition : Condition
  errorEntity : RuleErrorEntity
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  deriving Repr, DecidableEq

abbrev ResolvedFlatRule := ResolvedRule FlatCondition

/-- Caught evaluation failures emit without authored reference sets (predicate-family capture, KF522).
Polarity alone cannot distinguish that handler from a normal value-error verdict. -/
inductive RuleMessageOrigin where
  | condition
  | runtimeFailure
  deriving Repr, DecidableEq

/-- Emission retains the failure handler identity needed to derive reference sets from the checked rule. -/
structure FlatRuleMessage where
  errorAddress : RulePointer
  errorCode : String
  severity : ValidationSeverity
  messageType : Polarity
  origin : RuleMessageOrigin := .condition
  text : ResolvedMessageText
  deriving Repr, DecidableEq

namespace FlatRuleMessage

/-- Only ERROR severity makes the document invalid; warnings and infos still emit. -/
def invalidates (message : FlatRuleMessage) : Bool :=
  message.severity == .error

end FlatRuleMessage

/-- Whole-rule evaluation preserves both silent cases instead of collapsing them into `Option FlatRuleMessage`. -/
inductive FlatRuleOutcome where
  | notFired
  | fired (message : FlatRuleMessage)
  | unknown
  deriving Repr, DecidableEq

/-- Whole-rule partial execution keeps a rule-level skip distinct from every evaluated condition outcome, including clean nonfiring and UNKNOWN. -/
inductive PartialRuleOutcome where
  | skipped
  | evaluated (outcome : FlatRuleOutcome)
  deriving Repr, DecidableEq

namespace FlatRuleOutcome

/-- Forget message metadata while retaining the complete underlying condition verdict. -/
def verdict : FlatRuleOutcome → Verdict
  | .notFired => .notFired
  | .fired message => .fired message.messageType
  | .unknown => .unknown

/-- The emitted message, when there is one. This intentionally maps both distinct silent outcomes to `none`; use `verdict` when the distinction matters. -/
def message? : FlatRuleOutcome → Option FlatRuleMessage
  | .fired message => some message
  | .notFired | .unknown => none

end FlatRuleOutcome

namespace ResolvedRule

/-- Attach metadata after the verdict without requiring a physical row. Parallel and keyed
no-match addresses retain unknown coordinates (`spec/07` §2); they cannot be `CellAddr`s. -/
def emitAtCoordinates (rule : ResolvedRule Condition)
    (coordinates : List MessageRepetitionCoordinate) (verdict : Verdict) : FlatRuleOutcome :=
  match verdict with
  | .notFired => .notFired
  | .fired messageType =>
      .fired {
        errorAddress := { entity := rule.errorEntity, coordinates }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
      }
  | .unknown => .unknown

/-- Physical error paths are the concrete specialization of the shared message emitter. -/
def emitAt (rule : ResolvedRule Condition) (errorPath : List Nat)
    (verdict : Verdict) : FlatRuleOutcome :=
  rule.emitAtCoordinates (errorPath.map .concrete) verdict

/-- The whole-rule catch preserves its distinct reference behavior after the control effect is handled. -/
def emitRuntimeFailureAt (rule : ResolvedRule Condition) (errorPath : List Nat) : FlatRuleOutcome :=
  match rule.emitAt errorPath (.fired .value) with
  | .fired message => .fired { message with origin := .runtimeFailure }
  | other => other

/-- The whole-rule catch at coordinates that need not form a physical row, as a joined row's may not. -/
def emitRuntimeFailureAtCoordinates (rule : ResolvedRule Condition)
    (coordinates : List MessageRepetitionCoordinate) : FlatRuleOutcome :=
  match rule.emitAtCoordinates coordinates (.fired .value) with
  | .fired message => .fired { message with origin := .runtimeFailure }
  | other => other

/-- The established nonrepeatable emitter is the empty-path specialization. -/
def emit (rule : ResolvedRule Condition) (verdict : Verdict) : FlatRuleOutcome :=
  rule.emitAt [] verdict

/-- Evaluate a condition exactly once, then pass only its verdict and resolved error path to the shared emitter. -/
def evalWithAt (rule : ResolvedRule Condition) (errorPath : List Nat)
    (evaluate : Condition → Verdict) : FlatRuleOutcome :=
  rule.emitAt errorPath (evaluate rule.condition)

/-- Evaluate a condition exactly once, then pass only its verdict to the shared emitter. -/
def evalWith (rule : ResolvedRule Condition)
    (evaluate : Condition → Verdict) : FlatRuleOutcome :=
  rule.evalWithAt [] evaluate

/-- The established flat specialization. Keeping it on the underlying generic structure preserves dot notation after record updates. -/
def evalFull (rule : ResolvedRule FlatCondition) (context : FlatContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  rule.evalWith fun condition => condition.evalFull context hasContent

end ResolvedRule

end A12Kernel
