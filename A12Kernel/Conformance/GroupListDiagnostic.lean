import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.ValidationRule

/-! # A12Kernel.Conformance.GroupListDiagnostic — group-list admission diagnostic identity

The separating axis is that the shared account's *rule* list and the Kernel's *class* partition do
not line up. Three measured facts do the separating: the root-group classes are distinct from
overlap, the two duplicate classes are distinct, and one star draws different classes through
different carriers.

The fixture mirrors the measured kernel model rather than reusing a shared one, because the
distinctions need shapes a general iteration model does not carry: a **nonrepeatable** nested pair
(the only way to reach the ancestor class without the star gate firing first), a disjoint
nonrepeatable pair, and a repeatable group.
-/

namespace A12Kernel.Conformance.GroupListDiagnostic

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Probe", "A", "Deep"], name := "DeepVal",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Probe", "B"], name := "BVal",
        policy := { kind := .number unsigned } },
      { id := 4, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 5, groupPath := ["Other"], name := "OtherVal",
        policy := { kind := .number unsigned } }]
    -- `Hollow` declares no field anywhere below it, which a repeatable declaration can express.
    repeatableGroups := [{ level := 10, path := ["Probe", "Rows"] },
      { level := 20, path := ["Probe", "Hollow"] },
      { level := 30, path := ["Archive"] }] }

private def group (groups : GroupPath) : SurfaceGroupListOperand :=
  .group (.path { base := .absolute, groups })

private def rowsStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Probe" }, { name := "Rows", starred := true }] }

private def hollowStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Probe" }, { name := "Hollow", starred := true }] }

private def diagnostic? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) : Option KernelStaticDiagnostic :=
  match CheckedValidationCondition.fromGroupList probeModel ["Probe"] operator
      operands with
  | .ok _ => none
  | .error error => error.groupListDiagnostic?

private def diagnosticCode? (operator : GroupFillQuantifier) (operands : List SurfaceGroupListOperand) : Option String :=
  (diagnostic? operator operands).map KernelStaticDiagnostic.kernelCode

/- The exact same operand twice and an ancestor/descendant pair are **two** Kernel classes, and one
   local error carries both — the split is read off the paths it retains, not from a second
   constructor. Both operands are nonrepeatable here, so the star gate cannot pre-empt either. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "A"]] =
      some .duplicateParam1 := by
  native_decide

example :
    diagnostic? .allGroupsFilled
        [group ["Probe", "A"], group ["Probe", "A", "Deep"]] =
      some .duplicateParam2 := by
  native_decide

/- A root beside its own descendant is still the overlap class because that gate pre-empts the
   root-family gate. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe"], group ["Probe", "B"]] =
      some .duplicateParam2 := by
  native_decide

/- The second root separates the two root-family classes from overlap. -/
example :
    diagnosticCode? .allGroupsFilled [group ["Other"], group ["Probe", "B"]] = some "MVK_ROOT_GROUP_REFERENCED" ∧
    diagnosticCode? .atLeastOneGroupFilled [group ["Other"], group ["Probe", "B"]] = some "MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS" ∧
    diagnosticCode? .allGroupsFilled [group ["Other"]] = some "MVK_ROOT_GROUP_REFERENCED" ∧
    diagnosticCode? .atLeastOneGroupFilled [group ["Other"]] = none := by
  native_decide

/- A singleton under a quantifier that requires two operands, beside the singleton-admitting
   quantifier that never reaches the class. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"]] =
      some .paramSizeInvalid2 := by
  native_decide

example : diagnostic? .atLeastOneGroupFilled [group ["Probe", "A"]] = none := by
  native_decide

/- One star, two carriers, two classes: forbidden under a multi-operand quantifier, and *required*
   when a repeatable group is named without it. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], rowsStar] =
      some .noWildcardsGAllowed := by
  native_decide

example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "Rows"]] =
      some .noWildcard := by
  native_decide

/- An unknown path is separable from every overlap class, which is why the class is retained. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "Nope"]] =
      some .invalidEntity := by
  native_decide


/-! ## The filled-count carrier

The same operand relation, a different multiplicity class, and one shape the quantifiers do not
have: a single starred operand is admitted where a single unstarred one is not. -/

private def countDiagnostic? (groups : List GroupPath)
    (rowGroup : GroupPath := ["Probe"]) : Option KernelStaticDiagnostic :=
  let surface : SurfaceNumericComparison :=
    { op := .ordinary .greater
      left := .atom (.filledGroupCount
        (groups.map fun path => .fixed (.path { base := .absolute, groups := path })))
      right := .literal { value := 0, authoredScale := 0 } }
  match elaborateNumericComparison probeModel rowGroup surface with
  | .ok _ => none
  | .error error => error.groupCountDiagnostic?

/- A single fixed unstarred operand takes the count's own multiplicity class. A starred operand is
   admitted; the separate rule-owned projector covers the measured one-level error-locus matrix. -/
example : countDiagnostic? [["Probe", "A"]] = some .paramSizeInvalidGN := by
  native_decide

/- A repeatable operand beside another takes the star class, not the multiplicity class. -/
example :
    countDiagnostic? [["Probe", "A"], ["Probe", "Rows"]] = some .noWildcard := by
  native_decide

/- The operand relation is the same one the quantifiers use, split the same way. -/
example :
    countDiagnostic? [["Probe", "A"], ["Probe", "A"]] = some .duplicateParam1 := by
  native_decide

example :
    countDiagnostic? [["Probe", "A"], ["Probe", "A", "Deep"]] =
      some .duplicateParam2 := by
  native_decide

example :
    countDiagnostic? [["Probe"], ["Probe", "B"]] = some .duplicateParam2 := by
  native_decide

example :
    (countDiagnostic? [["Other"], ["Probe", "B"]]).map
        KernelStaticDiagnostic.kernelCode =
      some "MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS" := by
  native_decide

example :
    countDiagnostic? [["Probe", "A"], ["Probe", "Nope"]] = some .invalidEntity := by
  native_decide

/- Two disjoint fixed operands are the accepted control. -/
example : countDiagnostic? [["Probe", "A"], ["Probe", "B"]] = none := by
  native_decide

/- An empty starred group is read before every list gate, so it answers under all five quantifiers
   ahead of the star gate the three multi-operand ones apply, ahead of arity, and behind a populated
   star that the star gate alone would already refuse. The populated-star twin is that gate's own
   class, which is what attributes the rows to the operand read
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)). -/
example :
    [GroupFillQuantifier.allGroupsFilled, .notAllGroupsFilled, .groupsNotCollectivelyFilled,
      .atLeastOneGroupFilled, .noGroupFilled].map (fun operator =>
        (diagnostic? operator [hollowStar], diagnostic? operator [hollowStar, group ["Probe", "B"]])) =
      List.replicate 5 (some .groupIsEmpty, some .groupIsEmpty) ∧
    diagnostic? .allGroupsFilled [rowsStar, hollowStar] = some .groupIsEmpty ∧
    diagnostic? .allGroupsFilled [rowsStar, group ["Probe", "B"]] = some .noWildcardsGAllowed := by
  native_decide

/- A field operand's resolver failure reaches the group-list projection with the resolver's own class,
   beside a group operand that is admitted with a resolving field
   ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)). -/
private def fieldAt (base : PathBase) (groups : List String) (name : String) :
    SurfaceGroupListOperand :=
  .field { base, groups, field := name }

example :
    [fieldAt .absolute ["Probe"] "Nope", fieldAt .absolute ["Nope"] "AVal",
      fieldAt (.relative 0) [] "Nope", fieldAt (.relative 1) [] "AVal"].map (fun operand =>
        diagnostic? .atLeastOneGroupFilled [operand, group ["Probe", "B"]]) =
      [some .invalidEntity, some .invalidRootGroup, some .invalidEntity,
        some .tooManyParentGroups] ∧
    diagnostic? .atLeastOneGroupFilled
      [fieldAt .absolute ["Probe", "A"] "AVal", group ["Probe", "B"]] = none := by
  native_decide

/-! ## A group operand that does not resolve

The Kernel reads a group path segment by segment, as it reads a field path, so the class turns on
which segment missed. An undeclared first segment is the root class whatever follows it, a lone
segment and a declared group read at root position included; a later miss is the entity class, and a
parent walk above the root has its own. A starred operand answers first for an earlier star landing
on a nonrepeatable segment, a field included
([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)). -/

private def groupAt (base : PathBase) (groups : List String) : SurfaceGroupListOperand :=
  .group (.path { base, groups })

private def starAt (base : PathBase) (groups : List SurfaceStarGroupSegment) :
    SurfaceGroupListOperand :=
  .starredGroup { base, groups }

example :
    [groupAt .absolute ["Nope", "A"], groupAt .absolute ["Nope"], groupAt .absolute ["A"],
      groupAt .absolute ["Probe", "Nope"], groupAt (.relative 0) ["Nope"],
      groupAt (.relative 1) ["A"]].map (fun operand =>
        diagnostic? .atLeastOneGroupFilled [operand, group ["Probe", "B"]]) =
      [some .invalidRootGroup, some .invalidRootGroup, some .invalidRootGroup,
        some .invalidEntity, some .invalidEntity, some .tooManyParentGroups] := by
  native_decide

example :
    let seg (name : String) (starred := true) : SurfaceStarGroupSegment := { name, starred }
    [starAt .absolute [seg "Probe" false, seg "Nope"],
      starAt .absolute [seg "Nope" false, seg "Rows"],
      starAt .absolute [seg "Probe" false, seg "A", seg "Nope" false],
      starAt .absolute [seg "Probe" false, seg "A" false, seg "AVal", seg "Nope" false],
      starAt .absolute [seg "Probe", seg "Rows"],
      starAt (.relative 1) [seg "Rows"],
      starAt .absolute [seg "Probe" false, seg "A"]].map (fun operand =>
        diagnostic? .atLeastOneGroupFilled [operand]) =
      [some .invalidEntity, some .invalidRootGroup, some .invalidWildcard, some .invalidWildcard,
        some .invalidWildcard, some .tooManyParentGroups, some .invalidWildcard] ∧
    diagnostic? .atLeastOneGroupFilled [rowsStar] = none := by
  native_decide

/- The scalar presence carrier reads its one group operand through the same split, with its
   admitted control. -/
example :
    let presence (base : PathBase) (groups : List String) : Option KernelStaticDiagnostic :=
      match CheckedValidationCondition.fromGroupPresence probeModel ["Probe"]
          (.path { base, groups }) .filled with
      | .ok _ => none
      | .error error => error.groupListDiagnostic?
    [presence .absolute ["Nope", "A"], presence .absolute ["Nope"], presence .absolute ["A"],
      presence .absolute ["Probe", "Nope"], presence (.relative 0) ["Nope"],
      presence (.relative 1) ["A"], presence .absolute ["Probe", "A"]] =
      [some .invalidRootGroup, some .invalidRootGroup, some .invalidRootGroup,
        some .invalidEntity, some .invalidEntity, some .tooManyParentGroups, none] := by
  native_decide

/- The count carrier draws the same classes. A fixed-only list is read by the comparison carrier and
   a starred operand by the carrier that admits both forms in one list. -/
private def countOperandsDiagnostic? (operands : List SurfaceGroupCountOperand) :
    Option KernelStaticDiagnostic :=
  let surface : SurfaceNumericComparison :=
    { op := .ordinary .greater
      left := .atom (.filledGroupCount operands)
      right := .literal { value := 0, authoredScale := 0 } }
  match elaborateNumericComparison probeModel ["Probe"] surface with
  | .ok _ => none
  | .error error => error.groupCountDiagnostic?

private def starredCountDiagnostic? (operands : List SurfaceGroupCountOperand) :
    Option KernelStaticDiagnostic :=
  match elaborateMixedFilledGroupCountComparison probeModel ["Probe"] operands
      NumericComparisonOp.greater 0 with
  | .ok _ => none
  | .error error => error.groupCountDiagnostic?

example :
    let fixedAt (base : PathBase) (groups : GroupPath) : SurfaceGroupCountOperand :=
      .fixed (.path { base, groups })
    let starredAt (base : PathBase) (groups : GroupPath) : SurfaceGroupCountOperand :=
      .starred (.terminallyStarred base groups)
    [fixedAt .absolute ["Nope", "A"], fixedAt .absolute ["A"], fixedAt (.relative 0) ["Nope"],
      fixedAt (.relative 1) ["A"]].map (fun operand =>
        countOperandsDiagnostic? [operand, fixedAt .absolute ["Probe", "B"]]) =
      [some .invalidRootGroup, some .invalidRootGroup, some .invalidEntity,
        some .tooManyParentGroups] ∧
    [starredAt .absolute ["Probe", "Nope"], starredAt .absolute ["Nope", "Rows"],
      starredAt .absolute ["Probe", "A"], starredAt (.relative 1) ["Rows"]].map (fun operand =>
        starredCountDiagnostic? [operand]) =
      [some .invalidEntity, some .invalidRootGroup, some .invalidWildcard,
        some .tooManyParentGroups] := by
  native_decide

private def countAtDiagnostic? (rowGroup : GroupPath) (operands : List SurfaceGroupCountOperand) :
    Option (Option KernelStaticDiagnostic) :=
  let surface : SurfaceNumericComparison :=
    { op := .ordinary .greater
      left := .atom (.filledGroupCount operands)
      right := .literal { value := 0, authoredScale := 0 } }
  match elaborateNumericComparison probeModel rowGroup surface with
  | .ok _ => none
  | .error error => some error.groupCountDiagnostic?

/- From a rule inside `Rows` the walk passes a read of `Rows` itself, so the missing-star class is
   not the Kernel's there: a sole count draws the count's arity class, a paired one the
   negative-condition class unguarded and admission guarded
   ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-group-list-rnu-admission-correction),
   [inbound](../../docs/SOURCES.md#inbound-2026-09-26h-list-reads)). The comparison route, which sees
   no guard, refuses without a class; from the root the walk refuses and draws the missing star. -/
example :
    let g (gs : GroupPath) : SurfaceGroupCountOperand := .fixed (.path { base := .absolute, groups := gs })
    countAtDiagnostic? ["Probe", "Rows"] [g ["Probe", "Rows"], g ["Probe", "B"]] = some none ∧
    countAtDiagnostic? ["Probe", "Rows"] [g ["Probe", "Rows"]] = some none ∧
    countAtDiagnostic? ["Probe"] [g ["Probe", "Rows"], g ["Probe", "B"]] = some (some .noWildcard) ∧
    countAtDiagnostic? ["Probe", "Rows"] [g ["Probe", "B"], g ["Probe", "A"]] = none := by
  native_decide

/-- The whole rule `FieldFilled(A/AVal) And GroupFilled(<group>)` at the root: the presence carrier
    passes a repeatable group to rule assembly, which projects the walk's class. -/
private def presenceRuleClass (groups : GroupPath) : Option (Option KernelStaticDiagnostic) :=
  match CheckedValidationCondition.fromGroupPresence probeModel ["Probe"]
      (.path { base := .absolute, groups }) .filled with
  | .error error => some error.groupListDiagnostic?
  | .ok presence =>
      match (elaborate probeModel ["Probe"]
          (.fieldFilled { base := .relative 0, groups := ["A"], field := "AVal" })).toOption.bind
          (CheckedValidationCondition.fromFlat · |>.toOption) with
      | none => some none
      | some guard =>
          match guard.and presence with
          | .error _ => some none
          | .ok whole =>
              match assembleResolvedValidationRule probeModel whole 1 "EMPTY" .error
                  { parts := [] } with
              | .ok _ => none
              | .error error => some error.diagnostic?

/- An empty group's missing star answers ahead of its emptiness: the empty repeatable `Hollow`,
   unstarred, draws the walk's class through presence, a quantifier and the count, and so does the
   empty repeatable root `Archive`; starred, their reads pass and the emptiness answers, the root with
   its own class ([inbound](../../docs/SOURCES.md#inbound-2026-09-26k-empty-star)). The root class is
   measured on the count; the quantifier reads the operand by the same check, an assumption SG9
   records. -/
example :
    let hollow : SurfaceGroupCountOperand := .fixed (.path { base := .absolute, groups := ["Probe", "Hollow"] })
    let b : SurfaceGroupCountOperand := .fixed (.path { base := .absolute, groups := ["Probe", "B"] })
    let archiveStar : SurfaceGroupListOperand :=
      .starredGroup { base := .absolute, groups := [{ name := "Archive", starred := true }] }
    presenceRuleClass ["Probe", "Hollow"] = some (some .noWildcard) ∧
    presenceRuleClass ["Archive"] = some (some .noWildcard) ∧
    diagnostic? .atLeastOneGroupFilled [group ["Probe", "Hollow"], group ["Probe", "B"]] =
      some .noWildcard ∧
    countOperandsDiagnostic? [hollow, b] = some .noWildcard ∧
    starredCountDiagnostic? [.starred (.terminallyStarred .absolute ["Probe", "Hollow"])] =
      some .groupIsEmpty ∧
    starredCountDiagnostic? [.starred (.terminallyStarred .absolute ["Archive"])] =
      some .rootGroupIsEmpty ∧
    diagnostic? .atLeastOneGroupFilled [archiveStar] = some .rootGroupIsEmpty := by
  native_decide

end A12Kernel.Conformance.GroupListDiagnostic
