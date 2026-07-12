import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Semantics.Required — absolute required-field staging

This capsule implements only `spec/03` §4's non-repeatable, absolutely required case.
The editor declaration desugars to an unconditional generated `FieldNotFilled` rule.
That rule is evaluated against the base checked-cell context; only afterwards is the
validation-scoped `.required` finding exposed to authored rules. Repeatable and
parent-filled conditions are deliberately outside this fragment.
-/

namespace A12Kernel

/-- The only severity admitted by the generated `mandatoryField` rule in this capsule. -/
inductive MandatorySeverity where
  | error
  deriving Repr, DecidableEq

namespace MandatorySeverity

def render : MandatorySeverity → String
  | .error => "ERROR"

end MandatorySeverity

/-- The only message type admitted by the generated `mandatoryField` rule. This is kept
    separate from the internal `Polarity` result so metadata is not inferred from an
    evaluator outcome. -/
inductive MandatoryMessageType where
  | omission
  deriving Repr, DecidableEq

namespace MandatoryMessageType

def render : MandatoryMessageType → String
  | .omission => "OMISSION"

end MandatoryMessageType

/-- The message metadata exposed by this capsule. Generated-rule identity/name is not
    represented yet; this intentionally avoids a general rule/message schema before the
    elaboration and interpolation layers land. -/
structure MandatoryFieldMetadata where
  errorCode : String
  severity : MandatorySeverity
  messageType : MandatoryMessageType
  deriving Repr, DecidableEq

/-- Source declaration admitted by this capsule: an absolute required field with no
    repeatable ancestor. -/
structure AbsoluteRequiredDecl where
  target : FlatField
  deriving Repr, DecidableEq

/-- Direct source-level meaning of an absolute required declaration. -/
inductive AbsoluteRequiredOutcome where
  | notRequired
  | mandatory (metadata : MandatoryFieldMetadata)
  | unknown
  deriving Repr, DecidableEq

/-- The admitted generated rule for one absolute, non-repeatable required field. -/
structure AbsoluteRequiredRule where
  condition : FlatCondition
  metadata : MandatoryFieldMetadata
  deriving Repr, DecidableEq

/-- The message metadata required by the source declaration. -/
def mandatoryFieldMetadata : MandatoryFieldMetadata :=
  { errorCode := "mandatoryField"
    severity := .error
    messageType := .omission }

/-- Direct source denotation, independent of the generated core condition. -/
def AbsoluteRequiredDecl.evaluate (declaration : AbsoluteRequiredDecl)
    (baseContext : FlatContext) : AbsoluteRequiredOutcome :=
  match declaration.target.observeValidation baseContext with
  | .empty => .mandatory mandatoryFieldMetadata
  | .value _ => .notRequired
  | .unknown _ => .unknown
  | .poison _ => .unknown

/-- Interpret a generated rule as the source-level mandatory outcome. -/
def AbsoluteRequiredRule.evaluate (rule : AbsoluteRequiredRule)
    (baseContext : FlatContext) : AbsoluteRequiredOutcome :=
  match rule.condition.evalFull baseContext false with
  | .notFired => .notRequired
  | .fired _ => .mandatory rule.metadata
  | .unknown => .unknown

/-- Desugar an absolute required declaration. The condition is unconditional because
    `FieldNotFilled` is eligible on an otherwise content-free document. -/
def desugarAbsoluteRequired (declaration : AbsoluteRequiredDecl) : AbsoluteRequiredRule :=
  { condition := .fieldNotFilled declaration.target
    metadata := mandatoryFieldMetadata }

namespace FlatContext

/-- Attach the staged required finding at exactly one resolved field. -/
def withRequiredFindingAt (context : FlatContext) (field : FlatField) : FlatContext where
  read id :=
    if id = field.id then (context.read id).withFinding .required else context.read id

end FlatContext

/-- Both products of the two-pass boundary: the generated rule outcome from the base
    context and the context authored validations see afterwards. -/
structure AbsoluteRequiredResult where
  generated : AbsoluteRequiredRule
  mandatoryVerdict : Verdict
  authoredContext : FlatContext

/-- Run the absolute-required generated rule before attaching its validation-scoped
    finding. Ordinary invalid cells yield `unknown`, so they are not relabelled required.
    `false` is intentional: the absolute rule must still run on a blank document. -/
def applyAbsoluteRequired (field : FlatField) (baseContext : FlatContext) :
    AbsoluteRequiredResult :=
  let generated := desugarAbsoluteRequired { target := field }
  let mandatoryVerdict := generated.condition.evalFull baseContext false
  let authoredContext := match mandatoryVerdict with
    | .fired .omission => baseContext.withRequiredFindingAt field
    | _ => baseContext
  { generated, mandatoryVerdict, authoredContext }

end A12Kernel
