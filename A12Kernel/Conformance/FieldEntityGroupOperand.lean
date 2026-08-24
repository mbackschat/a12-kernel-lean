import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenEntityValueList
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # A12Kernel.Conformance.FieldEntityGroupOperand — the shared entity list's group slot

A group-scope operand is admitted by the shared entity-list checker, and the three gates it passes
through read **three different things**: arity reads the authored slots, the wildcard gate reads the
authored path, and the kind/category scans read the group's expansion. The cases below separate all
three, because reasoning from any one of them predicts the wrong verdict for the other two.

The headline separator is the last pair: a group operand and its own written-out expansion are two
different models. The group form is admitted where the expansion is rejected for the nested
repeatable level's missing star, so a consumer that normalizes one into the other emits a model the
Kernel refuses.

The Number family then **retains** the admitted slot rather than lowering it into expanded field
slots, because the wildcard gate above is exactly what makes those two forms different models.
Under **full validation** the uniqueness carrier and all four value aggregates then read the slot's
whole `(row × field)` extent, enumerated from the model's repeatability rather than from any star
plan, through one resolver none of them can bypass. Checked-document computation reuses that extent;
partial validation and the legacy raw-document routes still refuse rather than answering an empty
stream.
-/

namespace A12Kernel.Conformance.FieldEntityGroupOperand

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

/-- Number, String, Date, and mixed nonrepeatable subtrees plus one stacked repeatable pair.
    `Probe/A` carries a String only below a **nested** subgroup, so a direct-child expansion and the
    recursive one disagree on it; `Probe/B` is the pure-Number control that isolates every other
    gate from the kind scan. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Probe", "A", "Deep"], name := "DeepVal",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Probe", "A", "Deep"], name := "DeepText",
        policy := { kind := .string } },
      { id := 4, groupPath := ["Probe", "B"], name := "BVal",
        policy := { kind := .number unsigned } },
      { id := 5, groupPath := ["Probe", "B", "Sub"], name := "SubVal",
        policy := { kind := .number { scale := 2, signed := false } } },
      { id := 6, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 7, groupPath := ["Probe", "Rows", "Fees"], name := "FeeVal",
        policy := { kind := .number unsigned }, repeatableScope := [10, 11] },
      { id := 8, groupPath := ["Probe", "Milestones"], name := "ReportedOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 9, groupPath := ["Probe", "Milestones"], name := "SettledOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 10, groupPath := ["Probe", "Contact"], name := "Email",
        policy := { kind := .string } },
      { id := 11, groupPath := ["Probe", "Contact"], name := "Phone",
        policy := { kind := .string } },
      { id := 12, groupPath := ["Probe", "Mixed"], name := "Text",
        policy := { kind := .string } },
      { id := 13, groupPath := ["Probe", "Mixed"], name := "Date",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 14, groupPath := ["Probe", "Inspections"], name := "VisitedOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" },
        repeatableScope := [12] },
      { id := 15, groupPath := ["Probe", "Inspections"], name := "ClosedOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" },
        repeatableScope := [12] },
      { id := 16, groupPath := ["Probe", "Rows", "Fixed"], name := "First",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 17, groupPath := ["Probe", "Rows", "Fixed"], name := "Second",
        policy := { kind := .number unsigned }, repeatableScope := [10] }]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"] },
      { level := 11, path := ["Probe", "Rows", "Fees"] },
      { level := 12, path := ["Probe", "Inspections"] }] }

private def group (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def starredGroup (segments : List SurfaceStarGroupSegment) :
    SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups := segments }

private def field (groups : List String) (name : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field := name }

private def starField (segments : List SurfaceStarGroupSegment) (name : String) :
    SurfaceFieldEntityOperand :=
  .star { base := .absolute, groups := segments, field := name }

/-- Every case reads one carrier that routes through the shared checker, so a class reported here
    is the shared gate's and not this operator's own. -/
private def diagnosticAt? (rowGroup : GroupPath) (operands : List SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource probeModel rowGroup
          { first, rest } with
      | .ok _ => none
      | .error error => error.diagnostic?

private def diagnostic? (operands : List SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  diagnosticAt? ["Probe"] operands

/-! ## Arity reads the authored slots

A group slot is already-many by itself, so the single-operand class it escapes is exactly the one
its own single expanded field would draw. -/

example : diagnostic? [group ["Probe", "B"]] = none := by native_decide

example : diagnostic? [field ["Probe", "B"] "BVal"] = some .paramSizeInvalidN := by
  native_decide

/-! ## The wildcard gate reads the authored path

Both arms, on operands character-identical apart from the `*`. A repeatable group must carry it and
a nonrepeatable group must not, and the two refusals are distinct classes rather than one. -/

example : diagnostic? [group ["Probe", "Rows"]] = some .noWildcard := by
  native_decide

/- Group-list error-locus binding does not widen this entity-list carrier in that same row. -/
example : diagnosticAt? ["Probe", "Rows"] [group ["Probe", "Rows"]] =
      some .noWildcard := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] =
      none := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "B", starred := true }]] =
      some .invalidWildcard := by
  native_decide

/- Nested stars both survive: the operand reopens two stacked repeatable levels. -/
example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true },
      { name := "Fees", starred := true }]] = none := by
  native_decide

/-! ## A group operand and its written-out expansion are two different models

This is the pair a normalizing consumer gets wrong. The group form is admitted; the same extent
authored as explicit field operands is refused for the nested repeatable level's missing star, and
starring that level admits it again. Neither neighbouring gate predicts this — the expansion is what
the kind gate reads, and arity has no view of the explicit form at all.

The refusal is read as admitted-or-not rather than as a class: the Kernel reports `MVK_NO_WILDCARD`
for this shape on a field-fill quantifier, and no row places that class on this carrier, so the
shared projection deliberately names none for it. -/

private def shapeAdmitted (operands : List SurfaceFieldEntityOperand) : Bool :=
  match operands with
  | [] => false
  | first :: rest =>
      (elaborateFieldEntityShape probeModel ["Probe"] { first, rest }).toOption.isSome

private def shapeError? (operands : List SurfaceFieldEntityOperand) :
    Option FieldEntityShapeElabError :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateFieldEntityShape probeModel ["Probe"] { first, rest } with
      | .ok _ => none
      | .error error => some error

example :
    shapeAdmitted [starredGroup [{ name := "Probe" },
      { name := "Rows", starred := true }]] = true := by
  native_decide

example :
    shapeAdmitted [starField [{ name := "Probe" }, { name := "Rows", starred := true }] "RowVal",
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees" }] "FeeVal"] = false := by
  native_decide

example :
    shapeAdmitted [starField [{ name := "Probe" }, { name := "Rows", starred := true }] "RowVal",
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees", starred := true }] "FeeVal"] = true := by
  native_decide

/- A star may reach a nonrepeatable terminal group without another star. The group form and its
   explicit two-field expansion are both admitted by the measured shared-carrier boundary. -/
example :
    shapeAdmitted [starredGroup [{ name := "Probe" },
      { name := "Rows", starred := true }, { name := "Fixed" }]] = true ∧
    shapeAdmitted [
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fixed" }] "First",
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fixed" }] "Second"] = true := by
  native_decide

/- An unstarred repeatable level below the first star is the distinct refusal measured as
   `MVK_NO_WILDCARD`; starring that same level is the admitted control above. -/
example :
    diagnostic? [starField [{ name := "Probe" }, { name := "Rows", starred := true },
      { name := "Fees" }] "FeeVal"] = some .noWildcard := by
  native_decide

/-! ## The indirect arm fires between operands, the direct arm does not see them

Ancestor/descendant overlap is rejected across a group and a field below it and between two starred
groups, while the same starred group twice stays two independent authored occurrences. Both overlap
fixtures are pure Number, so a missing overlap gate would report `none` rather than a kind class. -/

example :
    diagnostic? [group ["Probe", "B"], group ["Probe", "B"]] =
      some .duplicateParam1 := by
  native_decide

/- Exact identity is checked in authored encounter order before strict overlap. These retain the
   owning witness rather than relying only on the shared diagnostic projection. -/
example :
    shapeError? [group ["Probe", "B"], group ["Probe", "B"],
      field ["Probe", "B", "Sub"] "SubVal"] =
      some (.duplicateGroupOperand ["Probe", "B"]) := by
  native_decide

example :
    shapeError? [group ["Probe", "B"],
      field ["Probe", "B", "Sub"] "SubVal",
      field ["Probe", "B", "Sub"] "SubVal",
      group ["Probe", "B"]] = some (.duplicateOperand 5) := by
  native_decide

example :
    shapeError? [group ["Probe", "B"], group ["Probe", "B"],
      field ["Probe", "B", "Sub"] "SubVal",
      field ["Probe", "B", "Sub"] "SubVal"] =
      some (.duplicateGroupOperand ["Probe", "B"]) := by
  native_decide

example :
    diagnostic? [group ["Probe", "B"], field ["Probe", "B", "Sub"] "SubVal"] =
      some .duplicateParam2 := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees", starred := true }]] = some .duplicateParam2 := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] = none := by
  native_decide

/- Two disjoint subtrees are not an overlap even across repetition shapes, which is what keeps the
   arm above from being a groupness refusal in disguise. -/
example :
    diagnostic? [group ["Probe", "B"],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] = none := by
  native_decide

/-! ## The kind and category scans read the expansion, recursively

`Probe/A` is Number in its direct children and String only inside a nested subgroup. Under the
Number carrier it therefore draws the mixing class, which a direct-child expansion would miss
entirely, while the pure-Number `Probe/B` passes both scans. A group declares no kind of its own, so
neither verdict can be read off the operand's own declaration. -/

example : diagnostic? [group ["Probe", "A"]] = some .varyingTypesNotAllowed := by
  native_decide

example : diagnostic? [group ["Probe", "A", "Deep"]] = some .varyingTypesNotAllowed := by
  native_decide

/-! ## The value-list kind class is operator-specific

The measured Date group and admitted String group differ only in their recursive expansion kind.
The two local non-laws prevent projecting the measured class from every group certification
failure or from any expansion that merely contains a Date. -/

private inductive StringLiteralListAdmission where
  | admitted
  | refused (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

private def stringLiteralListSurface (first : SurfaceFieldEntityOperand) :
    SurfaceTokenEntityStringLiteralValueListSource :=
  { quantifier := .atLeastOne
    fields := { first, rest := [] }
    values := ["x", "y"] }

private def stringLiteralListAdmission (first : SurfaceFieldEntityOperand) :
    StringLiteralListAdmission :=
  match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      (stringLiteralListSurface first) with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/- Measured by the real-kernel group-carrier admission sweep at a12-dmkits `e233548e`. -/
example :
    stringLiteralListAdmission (group ["Probe", "Milestones"]) =
      .refused (some .onlyStringEnumNumberAllowed) := by
  native_decide

/- The paired real-kernel control from the same sweep. -/
example :
    stringLiteralListAdmission (group ["Probe", "Contact"]) = .admitted := by
  native_decide

/- Translate/Explain retains the exact authored group slot, quantifier, and decoded literal list. -/
private def translatedStringLiteralList? :
    Option (ValueListQuantifier × GroupPath × Bool × List String) := do
  let checked ←
    (elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      (stringLiteralListSurface (group ["Probe", "Contact"]))).toOption
  let checkedGroup ← checked.fields.first.groupSlot?
  pure (checked.quantifier, checkedGroup.groupPath, checkedGroup.isStarred,
    checked.firstValue :: checked.restValues)

example :
    translatedStringLiteralList? =
      some (.atLeastOne, ["Probe", "Contact"], false, ["x", "y"]) := by
  native_decide

/- The same recursive kind mechanism also reaches the legal starred repetition shape. This is an
   internally checked specialization; external evidence for this exact diagnostic row is pending. -/
example :
    stringLiteralListAdmission
        (starredGroup [{ name := "Probe" },
          { name := "Inspections", starred := true }]) =
      .refused (some .onlyStringEnumNumberAllowed) := by
  native_decide

/- No retained row assigns the Date class to a Number-group refusal on this literal surface. -/
example :
    stringLiteralListAdmission (group ["Probe", "B"]) = .refused none := by
  native_decide

/- A heterogeneous group is not the measured homogeneous Date-group discriminator. -/
example :
    stringLiteralListAdmission (group ["Probe", "Mixed"]) = .refused none := by
  native_decide

/-! ## The checked list retains the authored slot rather than its expansion

A Translate or rule-refactoring consumer has to re-render the operand that was written, and the
written-out expansion is not a legal substitute for it, so lowering the slot would be unsound and
not merely lossy. These read the finished checked list: one authored slot, its authored path, and
its star bit — never two expanded field slots. -/

private def checkedSlots (operands : List SurfaceFieldEntityOperand) :
    Option (List (Option (GroupPath × Bool))) :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource probeModel ["Probe"]
          { first, rest } with
      | .error _ => none
      | .ok checked =>
          some (checked.operands.map fun operand =>
            operand.groupSlot?.map fun group => (group.groupPath, group.isStarred))

example :
    checkedSlots [group ["Probe", "B"]] = some [some (["Probe", "B"], false)] := by
  native_decide

example :
    checkedSlots [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] =
      some [some (["Probe", "Rows"], true)] := by
  native_decide

/- A field slot beside a group stays a field slot, so the two forms remain distinguishable in the
   checked list and a consumer never has to guess which one was authored. -/
example :
    checkedSlots [group ["Probe", "B"],
      field ["Probe", "A", "Deep"] "DeepVal"] =
      some [some (["Probe", "B"], false), none] := by
  native_decide

/-! ## Derived facts read the recursive expansion

`Probe/B` declares scale 0 directly and scale 2 only inside a nested subgroup, so the list's derived
scale separates the recursive extent from a direct-child one a second time — at the value domain
rather than at the kind gate. -/

private def scaleOf (operands : List SurfaceFieldEntityOperand) :
    Option NumericScaleSummary :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource probeModel ["Probe"]
          { first, rest } with
      | .error _ => none
      | .ok checked => some checked.scaleSummary

example : scaleOf [group ["Probe", "B"]] = some (NumericScaleSummary.field 2) := by
  native_decide

/-! ## The aggregate path certifies the expansion itself

`FieldValuesNotUnique` runs the shared category scan before certification, but the aggregates do
not, so their group slot is where the expansion's Number-valuedness is actually established. -/

private def aggregateAdmits (operands : List SurfaceFieldEntityOperand) : Bool :=
  match operands with
  | [] => false
  | first :: rest =>
      (elaborateNumberEntitySource probeModel ["Probe"] { first, rest }).toOption.isSome

example : aggregateAdmits [group ["Probe", "B"]] = true := by native_decide

example : aggregateAdmits [group ["Probe", "A"]] = false := by native_decide

/-! ## Runtime over the expansion is refused, not answered empty

An empty stream would read as "the group contributed no values", which is a wrong answer rather
than a missing one. The refusal is the honest boundary until the runtime capsule lands. -/

private def emptyDocument : Document :=
  { instantiatedRows := [], rawCells := fun _ => none }

private def sumEvaluates (operands : List SurfaceFieldEntityOperand) : Bool :=
  match operands with
  | [] => false
  | first :: rest =>
      match elaborateNumberEntitySource probeModel ["Probe"] { first, rest } with
      | .error _ => false
      | .ok checked =>
          (checked.evaluateAggregate .sum emptyDocument [] { read := fun _ => .empty }
            (fun _ _ => malformedCheckedCell) (fun _ _ => .empty)).toOption.isSome

/- The control matters as much as the case: an ordinary two-field list over the same model does
   evaluate, so the group's refusal is the group slot's and not a broken fixture. -/
example :
    sumEvaluates [field ["Probe", "B"] "BVal",
      field ["Probe", "A"] "AVal"] = true := by
  native_decide

example : sumEvaluates [group ["Probe", "B"]] = false := by native_decide

/-! ## The message reference channel publishes the expansion, never the group

Measured at a12-dmkits `8094f664`: recursive expansion, no pointer to the group itself, concrete
coordinates for the unstarred form. The slot reaches it through the same subtree query the checker
used, so the fields a consumer reads off the slot and the fields the channel publishes cannot
disagree. A nested subgroup's field is in the set, which is again the recursive-versus-direct-child
separator. -/

private def referencedFields (operands : List SurfaceFieldEntityOperand) :
    Option (List FieldId) :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource probeModel ["Probe"]
          { first, rest } with
      | .error _ => none
      | .ok checked =>
          (checked.referencePointers []).toOption.map fun pointers =>
            pointers.map (·.field)

example : referencedFields [group ["Probe", "B"]] = some [4, 5] := by native_decide

/- The same list authored as its two explicit fields publishes the same set, which is what makes the
   authored form recoverable only from the retained slot and not from this channel. -/
example :
    referencedFields [field ["Probe", "B"] "BVal",
      field ["Probe", "B", "Sub"] "SubVal"] = some [4, 5] := by
  native_decide

/-! ## The expansion-kind gate is the operator's own question, so one input draws three classes

This is the half that does **not** generalize. The star, arity, and duplicate gates above are the
shared checker's and report the same class through every carrier; the kind gate asks what *this*
operator does with the expansion's values, so a single group whose subtree contains a String is
`MVK_NO_NUMBER` to `Sum`, `MVK_NOT_SORTABLE` to the extrema, and
`MVK_STRING_ENUM_AND_NON_STRING_ENUM` to `NumberOfDifferentValues`. Reading one carrier's class off
a sibling is exactly the inference these rows exist to block. -/

private def aggregateDiagnostic? (op : NumericAggregateOp)
    (operands : List SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberEntitySource probeModel ["Probe"] { first, rest } with
      | .ok _ => none
      | .error error => error.aggregateDiagnostic? op

example :
    aggregateDiagnostic? .sum [group ["Probe", "A"]] = some .noNumber := by
  native_decide

example :
    aggregateDiagnostic? .maximum [group ["Probe", "A"]] = some .notSortable := by
  native_decide

example :
    aggregateDiagnostic? .minimum [group ["Probe", "A"]] = some .notSortable := by
  native_decide

example :
    aggregateDiagnostic? .distinctCount [group ["Probe", "A"]] =
      some .stringEnumAndNonStringEnum := by
  native_decide

/- The pure-Number group is admitted under every one of them, which keeps the rows above pinned to
   the expansion's kinds rather than to groupness. -/
example : aggregateDiagnostic? .sum [group ["Probe", "B"]] = none := by native_decide

/- The **explicit** list separates what does and does not carry across operand forms. Under the
   extrema the written-out list draws the same unsortable class as the group, which places that gate
   on the operand's kind; under `Sum` no row places a class on the explicit form, so it stays
   unprojected rather than inheriting the group's. -/
example :
    aggregateDiagnostic? .maximum [field ["Probe", "A"] "AVal",
      field ["Probe", "A", "Deep"] "DeepText"] = some .notSortable := by
  native_decide

example :
    aggregateDiagnostic? .sum [field ["Probe", "A"] "AVal",
      field ["Probe", "A", "Deep"] "DeepText"] = none := by
  native_decide

/-! ## `FieldValuesNotUnique` compares the group's whole `(row × field)` extent

The compared set is **neither per-row nor per-field**: a duplicate lying within one row across two
fields fires exactly as one across two rows does. The recursion needs no authored `*`, because the
iteration comes from the *model's* repeatability rather than from the star, and the set is bounded
by the **operand**, not by the rule's own row.

`spec/07` marks that scope rule as an observed contract rather than a derived one, and warns that an
implementation reusing its star machinery — or reading the extent off the rule's iterating group or
binding depth — gets it wrong. So these fixtures put the discriminating duplicate where a wrong
derivation would miss it: at **row 2** of a repeatable subgroup, never row 1. -/

private def rowsModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form", "Box"], name := "Direct",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Form", "Box", "Lines"], name := "Left",
        policy := { kind := .number unsigned }, repeatableScope := [20] },
      { id := 3, groupPath := ["Form", "Box", "Lines"], name := "Right",
        policy := { kind := .number unsigned }, repeatableScope := [20] }]
    repeatableGroups := [{ level := 20, path := ["Form", "Box", "Lines"] }] }

private def rowsPrepared :
    PreparedFlatStringContext rowsModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler rowsModel).toOption.get (by native_decide)

private def cell (field : FieldId) (row : List Nat) (value : Nat) :
    ClassifiedCellInput :=
  { address := { field, path := row }, stored := toString value,
    raw := .parsed (.num value) }

/-- Two instantiated rows of the nested repeatable subgroup, plus the nonrepeatable direct field. -/
private def boxVerdict? (cells : List ClassifiedCellInput) : Option Verdict := do
  let source ←
    (elaborateNumberValuesNotUniqueSource rowsModel ["Form"]
      { first := .group (.path { base := .absolute, groups := ["Form", "Box"] }),
        rest := [] }).toOption
  let document ←
    (checkDocument rowsPrepared "en_US"
      { instantiatedRows := [{ group := 20, path := [1] }, { group := 20, path := [2] }],
        cells }).toOption
  (CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
    source document []).toOption

/- All distinct across both rows and the direct field: silent. This control is what makes every
   firing below attributable to its own duplicate. -/
example :
    boxVerdict? [cell 1 [] 1, cell 2 [1] 2, cell 3 [1] 3, cell 2 [2] 4, cell 3 [2] 5] =
      some .notFired := by
  native_decide

/- A duplicate **within one row, across two fields** — the pairing a per-row-then-per-field
   traversal that compares each field separately would miss. It is in row 2, not row 1. -/
example :
    boxVerdict? [cell 1 [] 1, cell 2 [1] 2, cell 3 [1] 3, cell 2 [2] 4, cell 3 [2] 4] =
      some (.fired .value) := by
  native_decide

/- A duplicate **across two rows of the nested subgroup**, in one field. Neither row is row 1 for
   both halves, so a first-row-pinned extent misses it. -/
example :
    boxVerdict? [cell 1 [] 1, cell 2 [1] 2, cell 3 [1] 3, cell 2 [2] 2, cell 3 [2] 5] =
      some (.fired .value) := by
  native_decide

/- A duplicate between the **nonrepeatable direct field and a nested row**, which is the pair that
   fails if the direct child and the nested rows are collected into separate sets. -/
example :
    boxVerdict? [cell 1 [] 9, cell 2 [1] 2, cell 3 [1] 3, cell 2 [2] 4, cell 3 [2] 9] =
      some (.fired .value) := by
  native_decide

/-! ## The value aggregates read the same extent under full validation

They reach it through the same resolver, so no separate arm makes them work and none could make
them silently disagree. `Sum` is the sharpest lock: the extent is the direct field plus both fields
of both rows, `5 + 3 + 4 + 3 + 4`, and each wrong account lands on its own number — a
direct-child-only expansion answers 5, an extent that drops the nonrepeatable direct field answers
14, and a first-row-pinned one answers 11.

Checked-document computation now reuses this extent and observes its cached cells at computation
phase. External calibration covers the starred combiner route only; partial validation remains
outside this boundary. -/

private def boxCells : List ClassifiedCellInput :=
  [cell 1 [] 5, cell 2 [1] 3, cell 2 [2] 4, cell 3 [1] 3, cell 3 [2] 4]

private def boxSource : Option (CheckedNumberEntitySource rowsModel) :=
  (elaborateNumberEntitySource rowsModel ["Form"]
    { first := .group (.path { base := .absolute, groups := ["Form", "Box"] }),
      rest := [] }).toOption

private def boxDocument : Option (CheckedDocument rowsModel) :=
  (checkDocument rowsPrepared "en_US"
    { instantiatedRows := [{ group := 20, path := [1] }, { group := 20, path := [2] }],
      cells := boxCells }).toOption

private def boxAggregate? (op : NumericAggregateOp) : Option NumericOperand := do
  let source ← boxSource
  let document ← boxDocument
  (source.evaluateCheckedDocumentValidationAggregate op document []).toOption

example : boxAggregate? .sum = some (.value 19 { canGrow := false, canShrink := false }) := by
  native_decide

example : boxAggregate? .maximum = some (.value 5 { canGrow := false, canShrink := false }) := by
  native_decide

/- Three distinct values across five cells, which is the set reading again rather than a count. -/
example :
    boxAggregate? .distinctCount = some (.value 3 { canGrow := false, canShrink := false }) := by
  native_decide

/-! ## The extent's depth is the operand's own, in both directions

`spec/07` states one half — a rule authored deep whose operand names an ancestor still compares that
ancestor's whole extent — and warns that reading the depth off the rule's binding gets it wrong. The
other half is that reading no depth at all is *also* wrong, and it is the half a resolver that simply
ignores the environment fails silently.

`Outer` is repeatable and `Inner` is repeatable below it, so a star on `Inner` alone leaves a
repeatable level **above** the operand. That level stays bound by the rule's row: a duplicate lying
only *across* `Outer` rows is not in the operand's extent at all, while one inside the bound row's
`Inner` rows is. Nothing else in the family separates those two accounts, because every other fixture
has no repeatable level above the operand for the environment to fix. -/

private def stackedModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form", "Outer"], name := "Marker",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 2, groupPath := ["Form", "Outer", "Inner"], name := "Code",
        policy := { kind := .number unsigned }, repeatableScope := [10, 20] }]
    repeatableGroups := [
      { level := 10, path := ["Form", "Outer"] },
      { level := 20, path := ["Form", "Outer", "Inner"] }] }

private def stackedPrepared :
    PreparedFlatStringContext stackedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler stackedModel).toOption.get (by native_decide)

/-- Two `Outer` rows, each with two `Inner` rows. -/
private def stackedRows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def stackedCell (field : FieldId) (row : List Nat) (value : Nat) :
    ClassifiedCellInput :=
  { address := { field, path := row }, stored := toString value,
    raw := .parsed (.num value) }

/-- `FieldValuesNotUnique(/Form/Outer/Inner*)`, evaluated from one bound `Outer` row. -/
private def innerStarVerdict? (outer : Env) (cells : List ClassifiedCellInput) :
    Option Verdict := do
  let source ←
    (elaborateNumberValuesNotUniqueSource stackedModel ["Form", "Outer"]
      { first := starredGroup [{ name := "Form" }, { name := "Outer" },
          { name := "Inner", starred := true }]
        rest := [] }).toOption
  let document ←
    (checkDocument stackedPrepared "en_US"
      { instantiatedRows := stackedRows, cells }).toOption
  (CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
    source document outer).toOption

/-- The only equal pair spans the two `Outer` rows; every value inside a single row is distinct. -/
private def crossOuterDuplicate : List ClassifiedCellInput :=
  [stackedCell 1 [1] 1, stackedCell 1 [2] 2,
    stackedCell 2 [1, 1] 7, stackedCell 2 [1, 2] 8,
    stackedCell 2 [2, 1] 7, stackedCell 2 [2, 2] 9]

/- Bound to `Outer[1]`, the operand reaches `7, 8` and cannot fire. A resolver that enumerated the
   whole model's repeatability would reach all four cells and report the cross-row `7`. -/
example : innerStarVerdict? [(10, 1)] crossOuterDuplicate = some .notFired := by
  native_decide

/- The same from `Outer[2]`, so the silence above is the binding rather than an artifact of row 1. -/
example : innerStarVerdict? [(10, 2)] crossOuterDuplicate = some .notFired := by
  native_decide

/- The positive control on the same fixture and the same environment: a duplicate **inside** the
   bound row's `Inner` rows does fire, so the levels at and below the star stay free. Without it the
   two rows above would be satisfied by a resolver that reached nothing at all. -/
example :
    innerStarVerdict? [(10, 1)]
      [stackedCell 1 [1] 1, stackedCell 1 [2] 2,
        stackedCell 2 [1, 1] 7, stackedCell 2 [1, 2] 7,
        stackedCell 2 [2, 1] 5, stackedCell 2 [2, 2] 9] = some (.fired .value) := by
  native_decide

end A12Kernel.Conformance.FieldEntityGroupOperand
