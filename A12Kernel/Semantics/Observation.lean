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
  | temporal (kind : TemporalKind) (components : TemporalComponents)
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
  | registeredCustomValidation (rejection : RegisteredCustomRejection)
  deriving Repr, DecidableEq

def BaseFormalCause.toFormalCause : BaseFormalCause → FormalCause
  | .malformed => .malformed
  | .declaredConstraint => .declaredConstraint
  | .unsupportedCharacter => .unsupportedCharacter
  | .leadingOrTrailingSpace => .leadingOrTrailingSpace
  | .customValidation => .customValidation
  | .registeredCustomValidation rejection =>
      .registeredCustomValidation rejection

/-- Scalar-parser output at the formal-check boundary. `empty` means that no field
    placement exists; `presentEmpty` represents a physical placement with no raw value.
    `parsed` means the reduced capsule's preceding raw constraints have admitted the
    value; a parsed empty String also becomes present-empty below. A forbidden line
    break, pattern failure, or other rejected raw String must enter as `rejected`.
    `rejected` is present raw input that could not become a legal scalar value. -/
inductive RawCell (α : Type := Value) where
  | empty
  | presentEmpty
  | parsed (value : α)
  | rejected (cause : BaseFormalCause)
  deriving Repr, DecidableEq

/-- The representational invariant expected of checked cells: a parsed value requires a
    physical placement. A present placement may carry neither a parsed value nor a
    finding; that is the distinct present-empty state. A required finding may validly be
    attached to an absent cell in the later validation pass. -/
def CheckedCell.WellFormed {α : Type} (cell : CheckedCell α) : Prop :=
  cell.rawPresent = false → cell.parsed = none

/-- Whether a parsed value is legal for a field kind. A stored `false` Confirm is not
    legal; `false` is only the comparison substitution for an empty Confirm. -/
def FieldKind.accepts : FieldKind → Value → Bool
  | .number _, .num _ => true
  | .boolean, .bool _ => true
  | .confirm, .conf true => true
  | .string, .str _ => true
  | .temporal expected _, .temporal actual => expected == actual.kind
  | _, _ => false

/-- Project a parser result through one caller-supplied value admission step. The parser owns text decoding and raw constraints; this function owns placement and formal-cause construction once. -/
@[simp] def checkRawCellWith (classify : α → Except BaseFormalCause (Option β)) :
    RawCell α → CheckedCell β
  | .empty =>
      { rawPresent := false, parsed := none, findings := [] }
  | .presentEmpty =>
      { rawPresent := true, parsed := none, findings := [] }
  | .parsed value =>
      match classify value with
      | .ok checked =>
          { rawPresent := true, parsed := checked, findings := [] }
      | .error cause =>
          { rawPresent := true
            parsed := none
            findings := [cause.toFormalCause] }
  | .rejected cause =>
      { rawPresent := true, parsed := none, findings := [cause.toFormalCause] }

@[simp] private def admitScalarValue (policy : FieldPolicy)
    (value : Value) : Except BaseFormalCause (Option Value) :=
  match policy.kind, value with
  | .string, .str text =>
      let normalized := normalizeEvaluatedString text
      if normalized.isEmpty then .ok none else .ok (some (.str normalized))
  | _, _ =>
      if policy.kind.accepts value then .ok (some value) else .error .malformed

/-- Apply static scalar policy and collect formal findings before any phase reads the cell. A parsed value of the wrong kind is malformed at this boundary. An admitted parsed String receives its one-pass evaluated-cache normalization here; this function does not decide raw line-break permission. -/
def formalCheck (policy : FieldPolicy) (raw : RawCell) : CheckedCell :=
  checkRawCellWith (admitScalarValue policy) raw

/-- Project an already-decoded and declaration-admitted typed parser result. This identity admission is not a parser or constraint check: callers must construct `.parsed` only after those preceding obligations succeed. -/
def checkAdmittedRawCell (raw : RawCell α) : CheckedCell α :=
  checkRawCellWith (fun value => .ok (some value)) raw

/-- Add a finding discovered after scalar formal checking. Requiredness uses this staged
    boundary only after its generated mandatory condition has been evaluated. -/
def CheckedCell.withFinding {α : Type} (cell : CheckedCell α)
    (cause : FormalCause) : CheckedCell α :=
  { cell with findings := cell.findings ++ [cause] }

private def firstComputationFinding : List FormalCause → Option FormalCause
  | [] => none
  | .required :: rest => firstComputationFinding rest
  | cause :: _ => some cause

/-- Read a checked cell in the requested phase. Validation exposes the first finding as
    unknown. Computation ignores the validation-scoped required finding but turns any
    ordinary formal invalidity it actually reads into poison. -/
def observeCell {α : Type} (phase : Phase)
    (cell : CheckedCell α) : CellObservation α :=
  let finding := match phase with
    | .validation => cell.findings.head?
    | .computation => firstComputationFinding cell.findings
  match finding, cell.parsed with
  | some cause, _ => match phase with
    | .validation => .unknown cause
    | .computation => .poison cause
  | none, some value => .value value
  | none, none => .empty

/-- Read one already-decoded and declaration-admitted typed parser result through the shared checked boundary. -/
def observeAdmittedRawCell (phase : Phase) (raw : RawCell α) : CellObservation α :=
  observeCell phase (checkAdmittedRawCell raw)

end A12Kernel
