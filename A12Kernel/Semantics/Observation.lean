import A12Kernel.Cell
import A12Kernel.Semantics.String

/-! # A12Kernel.Semantics.Observation — formal checking and phase reads

The first executable semantics capsule begins at the scalar-parser boundary: input is
already classified as absent, successfully parsed, or rejected with a formal cause.
Text-to-scalar parsing is a separate later layer. This keeps the validation semantics
independent from concrete syntax while preserving every distinction needed by `spec/02`
§3 and `spec/03` §2/§4.
-/

namespace A12Kernel

/-- Field kinds admitted by the currently implemented scalar and operator capsules. -/
inductive FieldKind where
  | number (config : NumField)
  | boolean
  | confirm
  | string
  deriving Repr, DecidableEq

/-- Static scalar policy consumed once by formal checking. Requiredness is deliberately
    absent: it is conditional model sugar whose generated rule must run before its
    validation-scoped finding is attached. Empty substitution likewise belongs to the
    operator reading the checked cell. -/
structure FieldPolicy where
  kind : FieldKind
  deriving Repr, DecidableEq

/-- Causes admitted at the local scalar/formal-check boundary. Contextual findings such
    as requiredness, duplicate indices, and over-repetition are intentionally impossible
    here and enter only through their later model/document passes. -/
inductive BaseFormalCause where
  | malformed
  | declaredConstraint
  | unsupportedCharacter
  | leadingOrTrailingSpace
  | customValidation
  deriving Repr, DecidableEq

def BaseFormalCause.toFormalCause : BaseFormalCause → FormalCause
  | .malformed => .malformed
  | .declaredConstraint => .declaredConstraint
  | .unsupportedCharacter => .unsupportedCharacter
  | .leadingOrTrailingSpace => .leadingOrTrailingSpace
  | .customValidation => .customValidation

/-- Scalar-parser output at the formal-check boundary. `empty` means that no field
    placement exists; `presentEmpty` represents a physical placement with no raw value.
    `parsed` means the reduced capsule's preceding raw constraints have admitted the
    value; a parsed empty String also becomes present-empty below. A forbidden line
    break, pattern failure, or other rejected raw String must enter as `rejected`.
    `rejected` is present raw input that could not become a legal scalar value. -/
inductive RawCell where
  | empty
  | presentEmpty
  | parsed (value : Value)
  | rejected (cause : BaseFormalCause)
  deriving Repr, DecidableEq

/-- The representational invariant expected of checked cells: a parsed value requires a
    physical placement. A present placement may carry neither a parsed value nor a
    finding; that is the distinct present-empty state. A required finding may validly be
    attached to an absent cell in the later validation pass. -/
def CheckedCell.WellFormed (cell : CheckedCell) : Prop :=
  cell.rawPresent = false → cell.parsed = none

/-- Whether a parsed value is legal for a field kind. A stored `false` Confirm is not
    legal; `false` is only the comparison substitution for an empty Confirm. -/
def FieldKind.accepts : FieldKind → Value → Bool
  | .number _, .num _ => true
  | .boolean, .bool _ => true
  | .confirm, .conf true => true
  | .string, .str _ => true
  | _, _ => false

/-- Apply static scalar policy and collect formal findings before any phase reads the cell. A parsed value of the wrong kind is malformed at this boundary. An admitted parsed String receives its one-pass evaluated-cache normalization here; this function does not decide raw line-break permission. -/
def formalCheck (policy : FieldPolicy) : RawCell → CheckedCell
  | .empty =>
      { rawPresent := false, parsed := none, findings := [] }
  | .presentEmpty =>
      { rawPresent := true, parsed := none, findings := [] }
  | .parsed value =>
      match policy.kind, value with
      | .string, .str text =>
          let normalized := normalizeEvaluatedString text
          if normalized.isEmpty then
            { rawPresent := true, parsed := none, findings := [] }
          else
            { rawPresent := true, parsed := some (.str normalized), findings := [] }
      | _, _ =>
          if policy.kind.accepts value then
            { rawPresent := true, parsed := some value, findings := [] }
          else
            { rawPresent := true, parsed := none, findings := [.malformed] }
  | .rejected cause =>
      { rawPresent := true, parsed := none, findings := [cause.toFormalCause] }

/-- Add a finding discovered after scalar formal checking. Requiredness uses this staged
    boundary only after its generated mandatory condition has been evaluated. -/
def CheckedCell.withFinding (cell : CheckedCell) (cause : FormalCause) : CheckedCell :=
  { cell with findings := cell.findings ++ [cause] }

private def firstComputationFinding : List FormalCause → Option FormalCause
  | [] => none
  | .required :: rest => firstComputationFinding rest
  | cause :: _ => some cause

/-- Read a checked cell in the requested phase. Validation exposes the first finding as
    unknown. Computation ignores the validation-scoped required finding but turns any
    ordinary formal invalidity it actually reads into poison. -/
def observeCell (phase : Phase) (cell : CheckedCell) : CellObservation :=
  let finding := match phase with
    | .validation => cell.findings.head?
    | .computation => firstComputationFinding cell.findings
  match finding, cell.parsed with
  | some cause, _ => match phase with
    | .validation => .unknown cause
    | .computation => .poison cause
  | none, some value => .value value
  | none, none => .empty

end A12Kernel
