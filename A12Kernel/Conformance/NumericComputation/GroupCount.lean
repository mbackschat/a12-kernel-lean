import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Compute-arm fixed multi-group filled-count locks

`NumberOfFilledGroups` over fixed nonrepeatable operand groups answers differently in the two
arms over the *same* descendant cells: validation makes an erroneous group unavailable, while
computation counts it. Both arms here are derived from one shared per-group cell list, so
"the same cells" is structural rather than a hand-maintained pairing.

The counted rows are measured at a12-dmkits `677e2eb7` under accepted `EXP-2026-08-06-01`.
Static admission and its exact short-arity, duplicate, overlap, and missing-star diagnostics
are measured through the clean exact-source consistency route at `cd41ea94`; the cell-level
projections themselves are locked in `Conformance/GroupPresence.lean`. The subtree extent of a
single operand is measured on both arms at `e0bfd1f35` under accepted `SPEC-2026-08-30-01`, and its
nested formally invalid row at `c9679c901` under pending `SPEC-2026-08-30-02`.
-/

namespace A12Kernel.Conformance.NumericComputation.GroupCount

open A12Kernel

def detailsAmountId : FieldId := 0
def preferencesChoiceId : FieldId := 1
def nestedDetailId : FieldId := 2
def computedTargetId : FieldId := 3
def thirdGroupId : FieldId := 4

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

def computationModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn computedTargetId ["Root"] "Target"] }

def withComputedTarget (source : FlatModel) : FlatModel :=
  { source with
    fields := source.fields ++
      [numberIn computedTargetId ["Root"] "Target"] }

def selfReferentialComputationModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn computedTargetId ["Root", "Details"] "Target"] }

def nestedSelfReferentialComputationModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn computedTargetId ["Root", "Details", "Inner"] "Target"] }

/-- `Details` additionally owns a deeper descendant field, so it carries direct and nested
    content at once. The pure shell below is the case that separates the two accounts. -/
def nestedDescendantModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn nestedDetailId ["Root", "Details", "Inner"] "Deep"] }

def threeGroupModel : FlatModel :=
  { model with
    fields := model.fields ++
      [numberIn thirdGroupId ["Root", "Other"] "OtherValue"] }

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

def surfaceGroup (path : GroupPath) : SurfaceGroupReference :=
  .path { base := .absolute, groups := path }

def surfaceCount (groups : List GroupPath) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount (groups.map fun path => .fixed (surfaceGroup path)))

def checkedCountResultOf (groups : List GroupPath) (rows : Rows) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation computationModel ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error _ => none
  | .ok checked => checked.evaluate { read := rows.read } |>.toOption

def checkedCountErrorIn (source : FlatModel) (groups : List GroupPath) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation (withComputedTarget source) ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error error => some error
  | .ok _ => none

def checkedCountGroupsIn (source : FlatModel) (groups : List GroupPath) :
    Option (List ResolvedGroupReference) :=
  match elaborateNumericComputationOperation (withComputedTarget source) ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom (.numeric (.filledGroupCount resolved)) => some resolved
      | _ => none

def checkedCountResultIn (source : FlatModel) (groups : List GroupPath)
    (rows : Rows) : Option NumericComputationResult :=
  match elaborateNumericComputationOperation (withComputedTarget source) ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error _ => none
  | .ok checked => checked.evaluate { read := rows.read } |>.toOption

def checkedCountFaultIn (source : FlatModel) (groups : List GroupPath)
    (rows : Rows) : Option NumericComputationFault :=
  match elaborateNumericComputationOperation (withComputedTarget source) ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate { read := rows.read } with
      | .error fault => some fault
      | .ok _ => none

def generatedMismatchErrorOf (groups : List GroupPath) :
    Option GeneratedComputationValidationError :=
  match elaborateNumericComputationOperation computationModel ["Root"]
      computedTargetId (surfaceCount groups) with
  | .error _ => none
  | .ok checked =>
      match checked.generatedMismatchComparison none with
      | .error error => some error
      | .ok _ => none

def checkedCountDiagnosticIn (source : FlatModel) (groups : List GroupPath) :
    Option KernelStaticDiagnostic :=
  (checkedCountErrorIn source groups).bind
    NumericComputationElabError.groupCountDiagnostic?

def selfReferentialCountError : Option NumericComputationElabError :=
  match elaborateNumericComputationOperation selfReferentialComputationModel
      ["Root", "Details"] computedTargetId
      (surfaceCount [["Root", "Details"], ["Root", "Preferences"]]) with
  | .error error => some error
  | .ok _ => none

def nestedSelfReferentialCountError : Option NumericComputationElabError :=
  match elaborateNumericComputationOperation nestedSelfReferentialComputationModel
      ["Root", "Details", "Inner"] computedTargetId
      (surfaceCount [["Root", "Details"], ["Root", "Preferences"]]) with
  | .error error => some error
  | .ok _ => none

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

/- The real-kernel static route admits the same fixed, distinct, disjoint two-group shape as
   a Number computation, so the checked surface reaches the already measured compute-arm
   evaluator instead of refusing it before resolution. -/
example :
    checkedCountResultOf
      [["Root", "Details"], ["Root", "Preferences"]]
      malformedBeside = some (.value 2) := by
  native_decide

/- Successful checking retains the exact authored reference order and origin even though the
   resulting count is order-insensitive. -/
example :
    checkedCountGroupsIn model
      [["Root", "Preferences"], ["Root", "Details"]] =
      some [preferencesGroup, detailsGroup] := by
  native_decide

/- The ordinary computed-target self-reference gate reaches every field in a counted group
   subtree instead of degrading the otherwise recognized computation into incoherent core. -/
example : selfReferentialCountError = some (.targetSelfReference computedTargetId) := by
  native_decide

/- Reference traversal is subtree-based rather than direct-group equality. -/
example :
    nestedSelfReferentialCountError =
      some (.targetSelfReference computedTargetId) := by
  native_decide

/- The checked surface carries the subtree rule end to end: an operand owning a deeper
   descendant counts through it rather than failing computation preflight. Arm-crossing
   generated mismatch lowering remains unsupported, which is a separate boundary. -/
example :
    checkedCountResultIn nestedDescendantModel
        [["Root", "Details"], ["Root", "Preferences"]]
        malformedBeside = some (.value 2) ∧
      generatedMismatchErrorOf
        [["Root", "Details"], ["Root", "Preferences"]] =
        some (.conditionAssembly .incoherentCore) := by
  native_decide

/- The lower bound is not an exact-two rule: a third disjoint group, a nested terminal with
   its own direct field, and an operand that itself owns a deeper descendant all pass
   consistency checking. -/
example :
    checkedCountErrorIn threeGroupModel
        [["Root", "Details"], ["Root", "Preferences"], ["Root", "Other"]] =
        none ∧
      checkedCountErrorIn nestedDescendantModel
        [["Root", "Details", "Inner"], ["Root", "Preferences"]] = none ∧
      checkedCountErrorIn nestedDescendantModel
        [["Root", "Details"], ["Root", "Preferences"]] = none := by
  native_decide

/- Exact Kernel strings are part of the diagnostic identity, while a non-group computation
   refusal remains deliberately unmapped. -/
example :
    KernelStaticDiagnostic.kernelCode .paramSizeInvalidGN =
        "MVK_PARAMSIZE_INVALIDGN" ∧
      KernelStaticDiagnostic.kernelCode .duplicateParam1 =
        "MVK_DUPLICATE_PARAM1" ∧
      KernelStaticDiagnostic.kernelCode .duplicateParam2 =
        "MVK_DUPLICATE_PARAM2" ∧
      KernelStaticDiagnostic.kernelCode .noWildcard = "MVK_NO_WILDCARD" ∧
      NumericComputationElabError.groupCountDiagnostic?
        (.targetNotNumber computedTargetId) = none := by
  native_decide

/- The kernel distinguishes fixed-count authoring failures by diagnostic identity: short
   arity, exact duplication, ancestor overlap, and an unstarred repeatable group are four
   separate classes. Root beside any descendant is the same overlap class, not a separate
   root rejection. -/
example :
    checkedCountDiagnosticIn model [["Root", "Details"]] =
        some .paramSizeInvalidGN ∧
      checkedCountDiagnosticIn model
        [["Root", "Details"], ["Root", "Details"]] =
        some .duplicateParam1 ∧
      checkedCountDiagnosticIn nestedDescendantModel
        [["Root", "Details"], ["Root", "Details", "Inner"]] =
        some .duplicateParam2 ∧
      checkedCountDiagnosticIn model
        [["Root"], ["Root", "Details"]] =
        some .duplicateParam2 ∧
      checkedCountDiagnosticIn repeatableGroupModel
        [["Root", "Rows"]] =
        some .noWildcard := by
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

/- An operand owning both a direct field and a deeper descendant is counted through the whole
   subtree, the same extent the validation arm traverses. Here the direct field alone decides it,
   since the descendant is absent; the shell rows below separate the two accounts. -/
example :
    countIn nestedDescendantModel [detailsGroup, preferencesGroup] malformedBeside =
      some (.value 2) := by
  native_decide

/- Boundary: a group inside a repeatable scope is refused, since a scalar context has no
   instantiated row to observe. This arm is reached even with no direct field to reject. -/
example :
    faultIn repeatableGroupModel [repeatableGroup, preferencesGroup] bothFilled =
      some (.unsupportedGroupCount ["Root", "Rows"]) := by
  native_decide

/- Boundary: a group absent from the model is refused rather than counted as absent. -/
example :
    faultIn model [missingGroup, preferencesGroup] bothFilled =
      some (.unsupportedGroupCount ["Root", "Missing"]) := by
  native_decide

/- Boundary: the model-free resolved evaluator carries no model, so it cannot enumerate any
   group's fields and refuses every group operand. It carries its **own** class rather than the
   illegal-group one, because no single operand is at fault and a consumer's remedy differs: that
   one is an authoring boundary, this one a missing evaluation input. -/
example :
    (match ScalarComputationContext.readNumericComputationAtom
        { read := malformedBeside.read }
        (.filledGroupCount [detailsGroup, preferencesGroup]) with
      | .error fault => some fault
      | .ok _ => none) = some NumericComputationFault.groupCountNeedsModel := by
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


/-! ## The shell discriminator

A **shell** owns no direct field at all: its only field sits two levels down. That asymmetry
against the flat sibling is what separates the two accounts of a group-count operand, because
under a direct-children account a shell owns nothing and can never be filled. -/

def shellClauseId : FieldId := 5

def shellModel : FlatModel :=
  { fields := [
      numberIn preferencesChoiceId ["Root", "Preferences"] "Choice",
      numberIn shellClauseId ["Root", "Shell", "Terms"] "Clause"] }

/-- The same shell with its descendant subgroup repeatable instead of ordinary. -/
def repeatableShellModel : FlatModel :=
  { fields := [
      numberIn preferencesChoiceId ["Root", "Preferences"] "Choice",
      { numberIn shellClauseId ["Root", "Shell", "Rows"] "Clause" with
          repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Root", "Shell", "Rows"] }] }

def shellGroup : ResolvedGroupReference :=
  { path := ["Root", "Shell"], origin := .path }

def shellRead (clause preference : CheckedCell) : FieldId → CheckedCell := fun id =>
  if id == shellClauseId then clause
  else if id == preferencesChoiceId then preference
  else presentEmpty

def shellCountIn (target : FlatModel) (clause preference : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  ScalarComputationContext.readCheckedNumericComputationAtom
    (model := target) { read := shellRead clause preference }
    (.numeric (.filledGroupCount [shellGroup, preferencesGroup]))

def shellCount (clause preference : CheckedCell) : Option NumericComputationResult :=
  (shellCountIn shellModel clause preference).toOption

/- The discriminator: a group whose only field lies two levels down contributes to the count,
   so the operand reads content over the whole subtree. A direct-children account answers `1`
   here, because the shell would own nothing. -/
example : shellCount (filled 24) (filled 7) = some (.value 2) := by
  native_decide

/- The control. Emptying that descendant drops the count to `1`, so a count stuck at `1` above
   would not have satisfied the direct-children account for the wrong reason. -/
example : shellCount presentEmpty (filled 7) = some (.value 1) := by
  native_decide

/- The measured row for the two rules together: the shell's only field is a nested descendant
   **and** it is formally invalid, and the group still counts as filled. The invalid cell reaches
   the Kernel's own operand inventory and the count is unaffected, so a presence test is not a
   read at any depth. -/
example : shellCount malformed (filled 7) = some (.value 2) := by
  native_decide

/-- The validation arm over the shell's own descendant cell, with no repeatable row and full
    coverage, so formal invalidity is the only dimension left free. The cells are supplied here
    rather than derived, exactly as the direct-child pair above; the model-side derivation for
    this shape is exercised by the group-presence cases instead. -/
def shellValidationCount (clause preference : CheckedCell) : FilledGroupCount :=
  let state (cells : List CheckedCell) : GroupPresenceState :=
    ({ descendantCells := cells
       hasInstantiatedRow := false
       structuralError := false
       relevance := .fullyRelevant } : ResolvedGroupPresenceInput).derive
  numberOfFilledGroups [state [clause], state [preference]]

/- The arms diverge at the **nested** shape exactly as they do at a direct child, which is the
   nearest false generalization worth guarding: widening the compute arm's extent through the
   subtree says nothing about the validation arm's availability rule. Over the same shell cells
   the compute arm counts the malformed descendant as filled and the validation arm cannot answer
   at all. -/
example :
    (shellCount malformed (filled 7), shellValidationCount malformed (filled 7)) =
      (some (.value 2), .unknown) := by
  native_decide

/- The clean control on that same pair, so the divergence is the descendant cell's formal state
   and not the nesting: both arms answer two. -/
example :
    (shellCount (filled 24) (filled 7), shellValidationCount (filled 24) (filled 7)) =
      (some (.value 2), .value 2) := by
  native_decide

/- Boundary: a **repeatable** descendant keeps the refusal, and the measurement says why. The Kernel
   counts such a shell structurally — one instantiated row with no filled cell still makes it count —
   so the answer is not a wider cell scan but a different mechanism, and this cell-list projection
   cannot express row instantiation at all. -/
example :
    (match shellCountIn repeatableShellModel (filled 24) (filled 7) with
      | .error fault => some fault
      | .ok _ => none) = some (.unsupportedGroupCount ["Root", "Shell"]) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.GroupCount
