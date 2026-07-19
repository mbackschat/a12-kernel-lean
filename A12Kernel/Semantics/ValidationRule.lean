import A12Kernel.Semantics.FlatValidation

/-! # One flat validation-rule emission boundary

This capsule attaches whole-rule metadata to the existing flat condition verdict. Its low-level input assumes an already-lowered condition, resolved error-field ID, nonrepeatable context, and already-resolved per-instance text. It also defines the one-pass renderer intended to produce that text after firing from parser-independent, already-resolved message parts. Checked post-fire integration and model assembly are separate; authored-template parsing and legality, field lookup, locale and display conversion, repeatable addressing, partial validation, rule collections, and orchestration remain outside.
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

/-- One already-decoded rule-message part. Field references and `$` syntax have been checked before this point; replacement strings are opaque and are never parsed again. -/
inductive MessageRenderPart where
  | text (value : String)
  | fieldName (input : MessageNameInput)
  | fieldValue (input : MessageValueInput)
  deriving Repr, DecidableEq

namespace MessageRenderPart

def render : MessageRenderPart → String
  | .text value => value
  | .fieldName input => input.resolve
  | .fieldValue input => input.resolve

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

/-- One already-resolved flat rule instance. The checked layer proves the model, error-field, and nonrepeatable assumptions before using this semantic core. -/
structure ResolvedFlatRule where
  condition : FlatCondition
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  resolvedText : ResolvedMessageText
  deriving Repr, DecidableEq

/-- The message fields admitted by this flat capsule. Rule path, referenced fields, and fill-to-fix metadata remain outside. -/
structure FlatRuleMessage where
  errorAddress : CellAddr
  errorCode : String
  severity : ValidationSeverity
  messageType : Polarity
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

namespace ResolvedFlatRule

/-- Evaluate the error condition exactly once and attach metadata only to a fired verdict. This fragment rejects repeatable error fields, hence the empty repetition path. -/
def evalFull (rule : ResolvedFlatRule) (context : FlatContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  match rule.condition.evalFull context hasContent with
  | .notFired => .notFired
  | .fired messageType =>
      .fired {
        errorAddress := { field := rule.errorField, path := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.resolvedText
      }
  | .unknown => .unknown

end ResolvedFlatRule

end A12Kernel
