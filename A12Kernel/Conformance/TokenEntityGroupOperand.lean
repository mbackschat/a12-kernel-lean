import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # A12Kernel.Conformance.TokenEntityGroupOperand — the token carrier's group slot

The shared entity-list gates over a group operand are locked once, on the Number carrier, in
[`FieldEntityGroupOperand`](FieldEntityGroupOperand.lean). What is new here is everything the
**String/Enumeration** carrier owns on top of them.

The headline is the projection. A token cell's meaning depends on the declaration that stored it —
a String cell and an Enumeration cell are read through different operands — so a group slot cannot
carry one operand for its whole expansion. The separating pair below reads the same two cells twice:
once through the declaration that stored each, and once through the first expanded declaration's
operand, which is what a per-operand accessor would silently do. The two answers differ.

The rest fixes the boundary this carrier actually reached: the whole `(row × field)` extent under
full validation, and refusals on every route that cannot enumerate the group's instantiated rows.
-/

namespace A12Kernel.Conformance.TokenEntityGroupOperand

open A12Kernel

/-- `Bag` is the extent fixture: one String directly in the group and one inside a **repeatable**
    subgroup. `Mixed` is the projection fixture, deliberately Enumeration-**first** so that a
    first-slot-wins projection misreads the String rather than the other way round. `Bad` and `Num`
    place their offending kind only below a nested subgroup, so a direct-child expansion would miss
    both. `Boolies`, `Num`, and `Contact` form the homogeneous-wrong-kind, heterogeneous, and admitted
    control matrix for `FirstFilledValue`. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form", "Bag"], name := "Tag",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Form", "Bag", "Lines"], name := "Note",
        policy := { kind := .string }, repeatableScope := [20] },
      { id := 3, groupPath := ["Form", "Mixed"], name := "Kind",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"], categories := [] } },
      { id := 4, groupPath := ["Form", "Mixed"], name := "Word",
        policy := { kind := .string } },
      { id := 5, groupPath := ["Form", "Bad"], name := "Ok",
        policy := { kind := .string } },
      { id := 6, groupPath := ["Form", "Bad", "Deep"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 7, groupPath := ["Form", "Num"], name := "Label",
        policy := { kind := .string } },
      { id := 8, groupPath := ["Form", "Num", "Deep"], name := "Count",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 9, groupPath := ["Form"], name := "Loose",
        policy := { kind := .string } },
      { id := 10, groupPath := ["Form"], name := "Other",
        policy := { kind := .string } },
      { id := 11, groupPath := ["Form", "Boolies"], name := "Accepted",
        policy := { kind := .confirm } },
      { id := 12, groupPath := ["Form", "Boolies"], name := "Reviewed",
        policy := { kind := .confirm } },
      { id := 13, groupPath := ["Form", "Contact"], name := "Email",
        policy := { kind := .string } },
      { id := 14, groupPath := ["Form", "Contact"], name := "Phone",
        policy := { kind := .string } }]
    repeatableGroups := [{ level := 20, path := ["Form", "Bag", "Lines"] }] }

private def prepared :
    PreparedFlatStringContext probeModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler probeModel).toOption.get (by native_decide)

private def group (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Form"], field := name }

private def fieldAt (groups : GroupPath) (name : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field := name }

private def rows : List RowAddr :=
  [{ group := 20, path := [1] }, { group := 20, path := [2] }]

private def str (field : FieldId) (row : List Nat) (value : String) :
    ClassifiedCellInput :=
  { address := { field, path := row }, stored := value,
    raw := .parsed (.str value) }

private def enumCell (field : FieldId) (value : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := value,
    raw := .parsed (.enum value) }

/-! ## Static admission is this carrier's own question about the expansion

Arity still reads the authored slot, so one group is already-many where one field is not. The kind
and category scans read the expansion **recursively**, and on this carrier they classify against the
String/Enumeration families: a Number below a nested subgroup mixes categories, a Boolean is refused
outright, and an Enumeration beside a String is a mix rather than a refusal. -/

private def diagnostic? (operands : List SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateTokenValuesNotUniqueSource probeModel ["Form"]
          { first, rest } with
      | .ok _ => none
      | .error error => error.diagnostic?

example : diagnostic? [group ["Form", "Bag"]] = none := by native_decide

example : diagnostic? [field "Loose"] = some .paramSizeInvalidN := by
  native_decide

example :
    diagnostic? [group ["Form", "Bad"]] =
      some .onlyStringEnumNumberDateAllowed := by
  native_decide

example :
    diagnostic? [group ["Form", "Num"]] = some .varyingTypesNotAllowed := by
  native_decide

/- The String/Enumeration mix is this operator's refusal, not the family's: the same group is
   admitted by the shared token certification that the distinct count enters through, which is why
   the homogeneity obligation lives on `FieldValuesNotUnique` alone. -/
example :
    diagnostic? [group ["Form", "Mixed"]] = some .varyingTypesNotAllowed := by
  native_decide

/-! ## `FirstFilledValue` separates a homogeneous wrong kind from heterogeneous mixing

The real-kernel matrix at a12-dmkits `57ddd442` measures each group beside its exact explicit
expansion. A homogeneous Confirm expansion reports `MVK_NO_BOOLY_ALLOWED`; an ordinary evaluated
String/Number expansion reports `MVK_VARYING_TYPES_NOT_ALLOWED`; the homogeneous String control is
admitted. -/

private inductive FirstFilledDiagnosticDecision where
  | admitted
  | mapped (diagnostic : KernelStaticDiagnostic)
  | rejectedUnmapped
  deriving Repr, DecidableEq

private def firstFilledDiagnosticDecision
    (operands : List SurfaceFieldEntityOperand) :
    Option FirstFilledDiagnosticDecision :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateFirstFilledTokenSource probeModel ["Form"] { first, rest } with
      | .ok _ => some .admitted
      | .error error =>
          match error.diagnostic? with
          | some diagnostic => some (.mapped diagnostic)
          | none => some .rejectedUnmapped

example :
    firstFilledDiagnosticDecision [group ["Form", "Boolies"]] =
      some (.mapped .noBoolyAllowed) := by
  native_decide

example :
    firstFilledDiagnosticDecision [fieldAt ["Form", "Boolies"] "Accepted",
      fieldAt ["Form", "Boolies"] "Reviewed"] =
        some (.mapped .noBoolyAllowed) := by
  native_decide

example :
    firstFilledDiagnosticDecision [group ["Form", "Num"]] =
      some (.mapped .varyingTypesNotAllowed) := by
  native_decide

example :
    firstFilledDiagnosticDecision [fieldAt ["Form", "Num"] "Label",
      fieldAt ["Form", "Num", "Deep"] "Count"] =
        some (.mapped .varyingTypesNotAllowed) := by
  native_decide

example :
    firstFilledDiagnosticDecision [group ["Form", "Contact"]] =
      some .admitted := by
  native_decide

example :
    firstFilledDiagnosticDecision [fieldAt ["Form", "Contact"] "Email",
      fieldAt ["Form", "Contact"] "Phone"] = some .admitted := by
  native_decide

/- The shared duplicate gate precedes the measured kind projection, while an unmeasured
   Confirm/String combination remains a rejected but deliberately unmapped source. -/
example :
    firstFilledDiagnosticDecision [
      fieldAt ["Form", "Boolies"] "Accepted",
      fieldAt ["Form", "Boolies"] "Accepted"] =
        some (.mapped .duplicateParam1) ∧
    firstFilledDiagnosticDecision [
      fieldAt ["Form", "Boolies"] "Accepted", field "Loose"] =
        some .rejectedUnmapped := by
  native_decide

/-! ## The checked list retains the authored slot and its recursive expansion

A group is one authored slot, never two expanded field slots, and the expansion it carries reaches
into the repeatable subgroup without any authored `*`. -/

private def checkedSlots (operands : List SurfaceFieldEntityOperand) :
    Option (List (Option (GroupPath × Bool × List FieldId))) :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateTokenEntitySource probeModel ["Form"] { first, rest } with
      | .error _ => none
      | .ok checked =>
          some (checked.operands.map fun operand =>
            operand.groupSlot?.map fun slot =>
              (slot.groupPath, slot.isStarred, slot.slots.map (·.declaration.id)))

example :
    checkedSlots [group ["Form", "Bag"]] =
      some [some (["Form", "Bag"], false, [1, 2])] := by
  native_decide

example :
    checkedSlots [group ["Form", "Mixed"], field "Loose"] =
      some [some (["Form", "Mixed"], false, [3, 4]), none] := by
  native_decide

/-! ## Each cell is read through the declaration that stored it

`Mixed` declares an Enumeration and then a String, and both cells store the text `A`. Read through
their own declarations both are present. Read through the **first** expanded declaration's operand —
exactly what an accessor returning one operand per slot produces — the String cell becomes UNKNOWN,
because the Enumeration classifier rejects a raw `.str` payload.

The second case is not a hypothetical: it is the same resolved slot, projected the wrong way on
purpose, so the row separates the two accounts instead of merely asserting the right one. -/

private inductive Token where
  | present (value : String)
  | empty
  | unknown
  deriving Repr, DecidableEq

private def token : ValueListCell .token → Token
  | .present value => .present value
  | .empty => .empty
  | .unknown _ => .unknown

private def resolvedGroup? (groups : GroupPath)
    (cells : List ClassifiedCellInput) :
    Option (ResolvedCheckedTokenEntityOperand probeModel) := do
  let source ←
    (elaborateTokenEntitySource probeModel ["Form"]
      { first := group groups, rest := [] }).toOption
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  (source.first.resolveCheckedValidationOperand document []).toOption

private def perDeclarationTokens (groups : GroupPath)
    (cells : List ClassifiedCellInput) : Option (List (CellAddr × Token)) :=
  (resolvedGroup? groups cells).map fun resolved =>
    (resolved.addressedCells.map (·.address)).zip
      ((resolved.valueListSideAt .validation).cells.map token)

private def firstOperandTokens (groups : GroupPath)
    (cells : List ClassifiedCellInput) : Option (List Token) := do
  let resolved ← resolvedGroup? groups cells
  let leading ← resolved.projectedCells.head?.map Prod.fst
  pure (resolved.addressedCells.map fun (addressed : CheckedAddressedCell) =>
    token (leading.checkedValueListCellAt .validation addressed.cell))

private def mixedCells : List ClassifiedCellInput :=
  [enumCell 3 "A", str 4 [] "A"]

example :
    perDeclarationTokens ["Form", "Mixed"] mixedCells =
      some [({ field := 3, path := [] }, .present "A"),
            ({ field := 4, path := [] }, .present "A")] := by
  native_decide

example :
    firstOperandTokens ["Form", "Mixed"] mixedCells =
      some [.present "A", .unknown] := by
  native_decide

/- A group authors no read form, so its Enumeration members are read stored. The retained
   projections show that directly; `checkedTokenEntityGroup_projections_stored` proves it for every
   model rather than this one. -/
private def projections (groups : GroupPath) :
    Option (List (Option EnumerationProjectionRef)) :=
  match elaborateTokenEntitySource probeModel ["Form"]
      { first := group groups, rest := [] } with
  | .error _ => none
  | .ok checked => some checked.first.projectionRefs

example :
    projections ["Form", "Mixed"] = some [some .stored, none] := by native_decide

/-! ## `FieldValuesNotUnique` compares the group's whole `(row × field)` extent

The compared set spans the group's direct field and every instantiated row of its repeatable
subgroup. The discriminating duplicate sits at **row 2**, so an extent read off the rule's own row,
off a star plan, or pinned to the first repetition misses it. -/

private def bagVerdict? (cells : List ClassifiedCellInput) : Option Verdict := do
  let source ←
    (elaborateTokenValuesNotUniqueSource probeModel ["Form"]
      { first := group ["Form", "Bag"], rest := [] }).toOption
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  (source.evaluateCheckedDocumentValuesNotUnique document []).toOption

/- The control: all three cells distinct, so every firing below is attributable to its own
   duplicate rather than to the fixture. -/
example :
    bagVerdict? [str 1 [] "Z", str 2 [1] "X", str 2 [2] "Y"] = some .notFired := by
  native_decide

/- Between the group's **nonrepeatable direct field** and a nested row — the pair that fails when
   the direct child and the rows are collected into separate sets. -/
example :
    bagVerdict? [str 1 [] "Z", str 2 [1] "X", str 2 [2] "Z"] =
      some (.fired .value) := by
  native_decide

/- Between the two **rows** of the nested subgroup, in one field, with neither cell being the
   direct one. -/
example :
    bagVerdict? [str 1 [] "Z", str 2 [1] "X", str 2 [2] "X"] =
      some (.fired .value) := by
  native_decide

/-! ## Every route that cannot enumerate the rows refuses rather than answering empty

An empty stream reads as "the group contributed no values", which is a wrong answer rather than a
missing one. Partial validation additionally has no measured account of how relevance masks a group
extent. The direct control matters: the same routes serve an ordinary field slot on the same
model. -/

private def partialResolves (operand : SurfaceFieldEntityOperand) : Bool :=
  match elaborateTokenEntitySource probeModel ["Form"]
      { first := operand, rest := [field "Other"] } with
  | .error _ => false
  | .ok checked =>
      match checkDocument prepared "en_US"
          { instantiatedRows := rows,
            cells := [str 1 [] "Z", str 2 [1] "X", str 2 [2] "Z",
              str 9 [] "L", str 10 [] "M"] } with
      | .error _ => false
      | .ok document =>
          (checked.first.resolveCheckedPartialValidationOperand document []
            .full).toOption.isSome

example : partialResolves (field "Loose") = true := by native_decide

example : partialResolves (group ["Form", "Bag"]) = false := by native_decide

/-- Every raw-`Document` arm the token slot reaches, in one list so the claim covers the class
    rather than the one arm that happened to get a case. Order: full validation, partial validation,
    the partial value count, and the value count at computation phase. -/
private def rawRoutesResolve (operand : SurfaceFieldEntityOperand) : List Bool :=
  match elaborateTokenEntitySource probeModel ["Form"]
      { first := operand, rest := [field "Other"] } with
  | .error _ => []
  | .ok checked =>
      let document : Document := { instantiatedRows := [], rawCells := fun _ => none }
      let directRead : FieldId → CheckedCell := fun _ => malformedCheckedCell
      let starRead : Env → FieldId → CheckedCell := fun _ _ => malformedCheckedCell
      [ (checked.first.resolvedValidationSide document [] directRead
          starRead).toOption.isSome,
        (checked.first.resolvedPartialValidationSide document [] .full directRead
          starRead).toOption.isSome,
        (checked.first.resolvedPartialValueCountSide document [] .full directRead
          starRead).toOption.isSome,
        (checked.first.resolvedValueCountComputationSide document [] directRead
          starRead starRead).toOption.isSome ]

example :
    rawRoutesResolve (field "Loose") = [true, true, true, true] := by native_decide

example :
    rawRoutesResolve (group ["Form", "Bag"]) = [false, false, false, false] := by
  native_decide

/- `FirstFilledValue` refuses for a **second, independent** reason that outlives the raw route:
   `spec/07` pins encounter order across a group only as "a filled direct field precedes the nested
   rows", which orders neither two direct fields nor two nested subgroups. Even a checked-document
   route would have nothing to implement. -/
private def firstFilledResolves (operand : SurfaceFieldEntityOperand) : Bool :=
  match elaborateFirstFilledTokenSource probeModel ["Form"]
      { first := operand, rest := [field "Other"] } with
  | .error _ => false
  | .ok checked =>
      (checked.evaluatePartialFirstFilledValidation
        { instantiatedRows := [], rawCells := fun _ => none } [] .full
        (fun _ => malformedCheckedCell)
        (fun _ _ => malformedCheckedCell)).toOption.isSome

example : firstFilledResolves (field "Loose") = true := by native_decide

example : firstFilledResolves (group ["Form", "Bag"]) = false := by native_decide

/-! ## The message reference channel publishes the expansion, never the group

The token operand reaches the same shared group projection the Number carrier uses, so the two
carriers cannot disagree about how far a group reaches. Coordinates follow one depth rule, measured
at a12-dmkits `bffe9cca` on this very carrier: the direct field carries none and the field below the
repeatable subgroup carries a **wildcard**, from an empty environment that a concrete account could
not have satisfied. -/

private def referenced (groups : GroupPath) : Option (List MessagePointer) :=
  match elaborateTokenEntitySource probeModel ["Form"]
      { first := group groups, rest := [] } with
  | .error _ => none
  | .ok checked => (checked.first.referencePointers []).toOption

example :
    referenced ["Form", "Bag"] = some [
      { field := 1, coordinates := [] },
      { field := 2, coordinates := [.wildcard] }] := by
  native_decide

/- The nonrepeatable control on the same model: no level to wildcard, so no coordinate at all. -/
example :
    referenced ["Form", "Mixed"] = some [
      { field := 3, coordinates := [] },
      { field := 4, coordinates := [] }] := by
  native_decide

end A12Kernel.Conformance.TokenEntityGroupOperand
