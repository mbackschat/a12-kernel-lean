import A12Kernel.Elaboration.NumericComputation

/-! # Compute-arm fixed multi-group filled-count locks

`NumberOfFilledGroups` over fixed nonrepeatable operand groups answers differently in the two
arms over the *same* descendant cells: validation makes an erroneous group unavailable, while
computation counts it. Both arms here are derived from one shared per-group cell list, so
"the same cells" is structural rather than a hand-maintained pairing.

The counted rows are measured at a12-dmkits `677e2eb7` under accepted `EXP-2026-08-06-01`.
Static admission of the operand in a computation is a separate axis with no retained
observation and remains closed; the cell-level projections themselves are locked in
`Conformance/GroupPresence.lean`.
-/

namespace A12Kernel.Conformance.NumericComputation.GroupCount

open A12Kernel

def detailsAmountId : FieldId := 0
def preferencesChoiceId : FieldId := 1
def nestedDetailId : FieldId := 2

def numberPolicy : FieldPolicy := { kind := .number { scale := 0, signed := true } }

def numberIn (id : FieldId) (groupPath : GroupPath) (name : String) : FlatFieldDecl where
  id
  groupPath
  name
  policy := numberPolicy

/-- Two sibling fixed nonrepeatable groups, each with one direct Number child. This is the
    shape the retained observation covers. -/
def model : FlatModel :=
  { fields := [
      numberIn detailsAmountId ["Root", "Details"] "Amount",
      numberIn preferencesChoiceId ["Root", "Preferences"] "Choice"] }

/-- `Details` additionally owns a deeper descendant field. Nested descendants are outside the
    measured shape, so this model is the refusal boundary rather than a wider count. -/
def nestedDescendantModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn nestedDetailId ["Root", "Details", "Inner"] "Deep"] }

/-- A group reached only through a repeatable declaration, with no direct field of its own. -/
def repeatableGroupModel : FlatModel :=
  { fields := model.fields ++
      [{ numberIn nestedDetailId ["Root", "Rows"] "RowAmount" with
          repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Root", "Rows"] }] }

def detailsGroup : ResolvedGroupReference :=
  { path := ["Root", "Details"], origin := .path }

def preferencesGroup : ResolvedGroupReference :=
  { path := ["Root", "Preferences"], origin := .path }

def missingGroup : ResolvedGroupReference :=
  { path := ["Root", "Missing"], origin := .path }

def repeatableGroup : ResolvedGroupReference :=
  { path := ["Root", "Rows"], origin := .path }

/-- Fixtures pass through the real declaration checker, so a cell claimed to be malformed is
    malformed because `formalCheck` rejected its raw input, not because a literal says so. -/
def presentEmpty : CheckedCell := formalCheck numberPolicy .empty
def filled (amount : Rat) : CheckedCell := formalCheck numberPolicy (.parsed (.num amount))
def malformed : CheckedCell := formalCheck numberPolicy (.rejected .malformed)
def requiredEmpty : CheckedCell := presentEmpty.withFinding .required

/-- One assignment of cells to the two operand groups, consumed by both arms below. -/
structure Rows where
  details : CheckedCell
  preferences : CheckedCell

def Rows.read (rows : Rows) : FieldId → CheckedCell := fun id =>
  if id == detailsAmountId then rows.details
  else if id == preferencesChoiceId then rows.preferences
  else presentEmpty

def evaluateIn (target : FlatModel) (groups : List ResolvedGroupReference) (rows : Rows) :
    Except NumericComputationFault NumericComputationResult :=
  ScalarComputationContext.readCheckedNumericComputationAtom
    (model := target) { read := rows.read } (.numeric (.filledGroupCount groups))

/-- Project the value, so a fault and a value can never be confused by a missing `Decidable`
    instance on the error union. -/
def countIn (target : FlatModel) (groups : List ResolvedGroupReference) (rows : Rows) :
    Option NumericComputationResult :=
  (evaluateIn target groups rows).toOption

def faultIn (target : FlatModel) (groups : List ResolvedGroupReference) (rows : Rows) :
    Option NumericComputationFault :=
  match evaluateIn target groups rows with
  | .error fault => some fault
  | .ok _ => none

def countOf (rows : Rows) : Option NumericComputationResult :=
  countIn model [detailsGroup, preferencesGroup] rows

/-- The validation arm over the very same two cells, with no repeatable row and full
    coverage, so formal invalidity is the only dimension left free. -/
def validationCountOf (rows : Rows) : FilledGroupCount :=
  let state (cells : List CheckedCell) : GroupPresenceState :=
    ({ descendantCells := cells
       hasInstantiatedRow := false
       structuralError := false
       relevance := .fullyRelevant } : ResolvedGroupPresenceInput).derive
  numberOfFilledGroups [state [rows.details], state [rows.preferences]]

def malformedBeside : Rows := { details := malformed, preferences := filled 7 }
def bothFilled : Rows := { details := filled 3, preferences := filled 7 }
def bothEmpty : Rows := { details := presentEmpty, preferences := presentEmpty }
def requiredBeside : Rows := { details := requiredEmpty, preferences := filled 7 }

/- The measured row: one operand group carries malformed-only content and the other is clean
   and filled, and the count is the ordinary exact `2`. The formally unavailable group counts
   as filled. -/
example : countOf malformedBeside = some (.value 2) := by
  native_decide

/- The all-clean positive control takes the same `2`, so the measured row cannot be read as a
   count the rule never reached. -/
example : countOf bothFilled = some (.value 2) := by
  native_decide

/- The all-clean zero control takes exact `0` from two present-empty groups, so absence still
   decides the count while formal invalidity does not. -/
example : countOf bothEmpty = some (.value 0) := by
  native_decide

/- The inversion witness: over the same `Rows` the validation arm answers unavailable where
   the computation arm counts, and agrees with it only on the all-clean row. -/
example :
    (validationCountOf malformedBeside, validationCountOf bothFilled) =
      (.unknown, .value 2) := by
  native_decide

/- A second, independent inversion witness through a different observation branch: a
   required-and-empty descendant is erroneous for validation yet absent for the computing
   instance, because computation never reads the validation-scoped required finding. -/
example :
    countOf requiredBeside = some (.value 1) ∧
      validationCountOf requiredBeside = .unknown := by
  native_decide

def countPlusOne : AuthoredNumericExpr (CheckedNumericComputationAtom model) :=
  .binary .add
    (.atom (.numeric (.filledGroupCount [detailsGroup, preferencesGroup])))
    (.literal { value := 1, authoredScale := 0 })

/- The count is a first-class arithmetic operand rather than a special top-level form: it
   composes under binary arithmetic and carries the same measured `2` into the result. -/
example :
    (countPlusOne.evaluateCheckedComputation
      { read := malformedBeside.read }).toOption = some (.value 3) := by
  native_decide

/-- A refused group operand placed to the right of an operand whose cell poisons. Evaluation
    alone short-circuits on the left poison and never reaches the group; only the structural
    preflight can still report it. -/
def poisonThenRefusedCount :
    AuthoredNumericExpr (CheckedNumericComputationAtom model) :=
  .binary .add
    (.atom (.numeric (.field (numberIn detailsAmountId ["Root", "Details"] "Amount"))))
    (.atom (.numeric (.filledGroupCount [missingGroup, preferencesGroup])))

/- The preflight decides the group boundary ahead of any read, which is the whole reason it
   exists: bypassing it lets a left-operand poison hide the structural fault entirely. -/
example :
    (poisonThenRefusedCount.evaluateCheckedComputation
        { read := malformedBeside.read }).toOption = none ∧
      (poisonThenRefusedCount.lowerForEvaluation.evalComputation
        (ScalarComputationContext.readCheckedNumericComputationAtom
          { read := malformedBeside.read })).toOption =
        some (.poison .malformed) := by
  native_decide

/- Boundary: a deeper descendant field puts the operand outside the measured shape, so it is
   refused rather than counted through the subtree the validation arm traverses. -/
example :
    faultIn nestedDescendantModel [detailsGroup, preferencesGroup] malformedBeside =
      some .unsupportedGroupCount := by
  native_decide

/- Boundary: a group inside a repeatable scope is refused, since a scalar context has no
   instantiated row to observe. This arm is reached even with no direct field to reject. -/
example :
    faultIn repeatableGroupModel [repeatableGroup, preferencesGroup] bothFilled =
      some .unsupportedGroupCount := by
  native_decide

/- Boundary: a group absent from the model is refused rather than counted as absent. -/
example :
    faultIn model [missingGroup, preferencesGroup] bothFilled =
      some .unsupportedGroupCount := by
  native_decide

/- Boundary: the model-free resolved evaluator carries no model, so it cannot enumerate any
   group's fields and refuses every group operand. The fault is payload-free, so it does not
   distinguish this cause from an illegal group; that limit is recorded in SG13. -/
example :
    (match ScalarComputationContext.readNumericComputationAtom
        { read := malformedBeside.read }
        (.filledGroupCount [detailsGroup, preferencesGroup]) with
      | .error fault => some fault
      | .ok _ => none) = some NumericComputationFault.unsupportedGroupCount := by
  native_decide

/- The scalar run plan mirrors the scalar evaluator exactly: it now admits an in-shape group
   count and still refuses one whose operand is out of shape. -/
example :
    CheckedNumericComputationAtom.supportsScalarEvaluation
        (model := model) (.numeric (.filledGroupCount [detailsGroup, preferencesGroup])) =
      true ∧
      CheckedNumericComputationAtom.supportsScalarEvaluation
        (model := model) (.numeric (.filledGroupCount [missingGroup, preferencesGroup])) =
        false := by
  native_decide

end A12Kernel.Conformance.NumericComputation.GroupCount
