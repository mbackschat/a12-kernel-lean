import A12Kernel.Semantics.FlatValidation

/-! # One flat validation-rule emission boundary

This capsule attaches whole-rule metadata to the existing flat condition verdict. Its low-level input assumes an already-lowered condition, resolved error-field ID, nonrepeatable context, and already-resolved per-instance text. Checked model assembly is separate; interpolation, authored templates, repeatable addressing, partial validation, rule collections, and orchestration remain outside.
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

/-- One already-resolved flat rule instance. The checked layer proves the model, error-field, and nonrepeatable assumptions before using this semantic core. -/
structure ResolvedFlatRule where
  condition : FlatCondition
  errorField : FieldId
  severity : ValidationSeverity
  resolvedText : ResolvedMessageText
  deriving Repr, DecidableEq

/-- The externally meaningful fields of one emitted authored-rule message in the flat fragment. -/
structure FlatRuleMessage where
  errorAddress : CellAddr
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
        severity := rule.severity
        messageType
        text := rule.resolvedText
      }
  | .unknown => .unknown

end ResolvedFlatRule

end A12Kernel
