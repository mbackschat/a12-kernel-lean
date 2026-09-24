import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Elaboration.StringComputation

/-! # Per-row operands on a fixed-target computation

A star leaves the repeatable levels above its first star to be bound by its evaluation, and a plain
read or a fixed group operand leaves every level its path crosses. On this arm the target repeats at
no level, so any such level is refused, and the Kernel's class is decided by who binds the outermost
one: the repeatable declaring group, nobody over an index-keyed group, or nobody. The String arm
answers from the same table. A level left unstarred below the first star is refused with the
missing-star class whatever binds it. Every expected value is a `computation add --dry-run` verdict
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)).
-/

namespace A12Kernel.Conformance.NumericComputation.StarBinding

open A12Kernel

private def number (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath, name, policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := scope }

private def boxes : GroupPath := ["Probe", "Batches", "Boxes"]

/-- `Batches` (level 10) holding `Boxes` (level 11), with a key field in each so the index
    declaration can move between them while the fields stay put. -/
private def modelWith (batchesKey boxesKey : Option FieldId) : FlatModel :=
  { fields := [
      number 1 ["Probe"] "W", number 2 ["Probe", "Out"] "Free",
      number 3 ["Probe", "Batches"] "BW" [10],
      { id := 4, groupPath := ["Probe", "Batches"], name := "Key", policy := { kind := .string },
        repeatableScope := [10] },
      number 5 boxes "Amt" [10, 11],
      { id := 6, groupPath := boxes, name := "Name", policy := { kind := .string },
        repeatableScope := [10, 11] },
      number 7 (boxes ++ ["BSeal"]) "Seal" [10, 11],
      { id := 8, groupPath := boxes, name := "Flag", policy := { kind := .boolean },
        repeatableScope := [10, 11] },
      number 9 boxes "Amt2" [10, 11],
      { id := 10, groupPath := boxes, name := "BKey", policy := { kind := .string },
        repeatableScope := [10, 11] },
      { id := 11, groupPath := ["Probe", "Batches"], name := "BText", policy := { kind := .string },
        repeatableScope := [10] },
      number 12 ["Probe", "Batches", "Seal2"] "S2" [10],
      { id := 13, groupPath := ["Probe", "Out"], name := "FreeS", policy := { kind := .string } }]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Batches"], repeatability := some 2,
        indexField := batchesKey },
      { level := 11, path := boxes, repeatability := some 2, indexField := boxesKey }] }

private def model : FlatModel := modelWith none none

/-- The outer level `Batches` is index-keyed. -/
private def outerKeyed : FlatModel := modelWith (some 4) none

/-- Only the reopened inner level `Boxes` is index-keyed. -/
private def innerKeyed : FlatModel := modelWith none (some 10)

/-- Which levels carry a star, and whether the path is spelled from the declaring group. -/
inductive Shape where
  | bothStarred | outerUnstarred | innerUnstarred | relativeInner
  deriving Repr, DecidableEq

private def segments : Shape → PathBase × List SurfaceStarGroupSegment
  | .bothStarred => (.absolute,
      [{ name := "Probe" }, { name := "Batches", starred := true }, { name := "Boxes", starred := true }])
  | .outerUnstarred => (.absolute,
      [{ name := "Probe" }, { name := "Batches" }, { name := "Boxes", starred := true }])
  | .innerUnstarred => (.absolute,
      [{ name := "Probe" }, { name := "Batches", starred := true }, { name := "Boxes" }])
  | .relativeInner => (.relative 0, [{ name := "Boxes", starred := true }])

private def starField (shape : Shape) (field : String) : SurfaceStarFieldPath :=
  let (base, groups) := segments shape
  { base, groups, field }

private def entity (shape : Shape) (field : String) : SurfaceNumberEntitySource :=
  { first := .star (starField shape field), rest := [] }

private def rootW : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Probe"], field := "W" }

inductive Carrier where
  | sum | max | firstFilled | tokenCount | booleanCount | products | groupCount
  deriving Repr, DecidableEq

private def carriers : List Carrier :=
  [.sum, .max, .firstFilled, .tokenCount, .booleanCount, .products, .groupCount]

private def expression (shape : Shape) :
    Carrier → AuthoredNumericExpr SurfaceNumericComputationAtom
  | .sum => .atom (.numeric (.aggregate .sum (entity shape "Amt")))
  | .max => .atom (.numeric (.aggregate .maximum (entity shape "Amt")))
  -- The measured rows read the star beside a root field.
  | .firstFilled => .atom (.firstFilled { entity shape "Amt" with rest := [rootW] })
  | .tokenCount => .atom (.tokenValueCount "x"
      { first := .star (starField shape "Name") .stored, rest := [] })
  | .booleanCount => .atom (.booleanValueCount true (entity shape "Flag"))
  | .products => .atom (.sumOfProducts
      { left := starField shape "Amt", right := starField shape "Amt2" })
  | .groupCount =>
      let (base, groups) := segments shape
      .atom (.numeric (.filledGroupCount [.starred { base, groups := groups ++ [{ name := "BSeal" }] }]))

/-- Each carrier projects through its own established classes; the gate's classes come last. -/
private def classOf : NumericComputationElabError → Option KernelStaticDiagnostic
  | .aggregate (.shape error) => error.diagnostic?
  | .productAggregate error => error.diagnostic?
  | .tokenValueCount (.source error) => error.diagnostic?
  | .booleanValueCount (.shape error) => error.diagnostic?
  | error => error.iterationDiagnostic? <|> error.groupCountDiagnostic?

/-- `none` when admitted, otherwise the refusal's class, for a computation into the fixed `Free`. -/
private def admission (m : FlatModel) (declaringGroup : GroupPath)
    (e : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (Option KernelStaticDiagnostic) :=
  match elaborateCompleteNumericComputationOperation m declaringGroup 2 e with
  | .ok _ => none
  | .error error => some (classOf error)

private def row (m : FlatModel) (declaringGroup : GroupPath) (shape : Shape) :
    List (Option (Option KernelStaticDiagnostic)) :=
  carriers.map fun carrier => admission m declaringGroup (expression shape carrier)

private def out : GroupPath := ["Probe", "Out"]
private def batches : GroupPath := ["Probe", "Batches"]

/- Both levels starred is admitted except by `SumOfProducts`, which requires its lone star at the
   lowest level. Leaving the outer level unstarred from a nonrepeatable declaring group draws the
   missing-star class on all seven; six of them used to admit it and fail only at evaluation, on a
   missing binding. -/
example :
    row model out .bothStarred =
      [none, none, none, none, none, some (some .wildcardOnlyAtLowestLevelAllowed), none] ∧
    row model out .outerUnstarred = carriers.map (fun _ => some (some .noWildcard)) := by
  native_decide

/- The inner level unstarred below the first star is the missing-star class on every carrier, and
   an index declared on either level does not move it. -/
example :
    row model out .innerUnstarred = carriers.map (fun _ => some (some .noWildcard)) ∧
    admission outerKeyed out (expression .innerUnstarred .sum) = some (some .noWildcard) ∧
    admission innerKeyed out (expression .innerUnstarred .sum) = some (some .noWildcard) := by
  native_decide

/- A repeatable declaring group that binds the outer level makes the star a per-row read, so the
   containment class answers, in the relative spelling on every carrier and in the absolute one. -/
example :
    row model batches .relativeInner = carriers.map (fun _ => some (some .fieldNotInRuleGroup)) ∧
    admission model batches (expression .outerUnstarred .sum) =
      some (some .fieldNotInRuleGroup) := by
  native_decide

/- An unbound outer level draws the index class exactly when that level is index-keyed. An index on
   the reopened inner level changes nothing, a keyed level the declaring group binds still draws
   containment, and the fully starred control stays admitted. -/
example :
    [admission outerKeyed out (expression .outerUnstarred .sum),
      admission outerKeyed out (expression .outerUnstarred .groupCount),
      admission innerKeyed out (expression .outerUnstarred .sum),
      admission outerKeyed batches (expression .relativeInner .sum),
      admission outerKeyed out (expression .bothStarred .sum)] =
    [some (some .errorFieldNoIndex), some (some .errorFieldNoIndex), some (some .noWildcard),
      some (some .fieldNotInRuleGroup), none] := by
  native_decide

/- The per-row class answers ahead of target self-reference whichever operand reads the target, and
   a star's unbound level answers ahead of a duplicate elsewhere in its list in either order, the
   whole list being judged before the duplicate scan; `W` twice alone is the duplicate control. -/
example :
    let free : AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.field { base := .absolute, groups := ["Probe", "Out"], field := "Free" }))
    let perRow := expression .relativeInner .sum
    let sumOf (operands : List SurfaceFieldEntityOperand) :
        AuthoredNumericExpr SurfaceNumericComputationAtom :=
      match operands with
      | first :: rest => .atom (.numeric (.aggregate .sum { first, rest }))
      | [] => .literal { value := 0, authoredScale := 0 }
    let outerStar : SurfaceFieldEntityOperand := .star (starField .outerUnstarred "Amt")
    [admission model batches (.binary .add free perRow),
      admission model batches (.binary .add perRow free),
      admission model out (sumOf [outerStar, rootW, rootW]),
      admission model out (sumOf [rootW, rootW, outerStar]),
      admission model out (sumOf [rootW, rootW])] =
    [some (some .fieldNotInRuleGroup), some (some .fieldNotInRuleGroup),
      some (some .noWildcard), some (some .noWildcard), some (some .duplicateParam1)] := by
  native_decide

private def contained : Option (Option KernelStaticDiagnostic) := some (some .fieldNotInRuleGroup)
private def missingStar : Option (Option KernelStaticDiagnostic) := some (some .noWildcard)
private def noIndex : Option (Option KernelStaticDiagnostic) := some (some .errorFieldNoIndex)

private def absoluteField (groups : List String) (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

private def relativeField (groups : List String) (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups, field := name }

private def plusOne (reference : SurfaceFieldPath) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .binary .add (.atom (.numeric (.field reference))) (.literal { value := 1, authoredScale := 0 })

private def bText : SurfaceFieldPath := absoluteField ["Probe", "Batches"] "BText"

/- A plain read follows the star's table on every leaf that reads a field: containment from the
   group that binds its outermost level, whether its deeper level is bound or not, and otherwise the
   missing-star or index class. -/
example :
    let bwAbsolute := absoluteField ["Probe", "Batches"] "BW"
    let length (reference : SurfaceFieldPath) :
        AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.stringLength reference))
    let asNumber : AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.fieldValueAsNumber (.direct bText)))
    [admission model batches (plusOne (relativeField [] "BW")),
      admission model out (plusOne bwAbsolute),
      admission outerKeyed out (plusOne bwAbsolute),
      admission model batches (plusOne (relativeField ["Boxes"] "Amt")),
      admission model boxes (plusOne bwAbsolute),
      admission model batches (length bText),
      admission model out (length bText),
      admission outerKeyed out (length bText),
      admission model batches asNumber,
      admission model out asNumber,
      admission outerKeyed out asNumber,
      admission model batches (length (relativeField ["Boxes"] "Name"))] =
    [contained, missingStar, noIndex, contained, contained, contained, missingStar, noIndex,
      contained, missingStar, noIndex, contained] := by
  native_decide

/- A fixed group operand follows it too, a repeatable group named without its star included, and
   the class answers ahead of the count's arity minimum and beside a star. -/
example :
    let fixedGroup (base : PathBase) (groups : List String) : SurfaceGroupCountOperand :=
      .fixed (.path { base, groups })
    let outGroup := fixedGroup .absolute ["Probe", "Out"]
    let countOf (operands : List SurfaceGroupCountOperand) :
        AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.filledGroupCount operands))
    let sealAbsolute := fixedGroup .absolute ["Probe", "Batches", "Seal2"]
    let batchesGroup := fixedGroup .absolute ["Probe", "Batches"]
    let (starBase, starGroups) := segments .bothStarred
    let starredSeal : SurfaceGroupCountOperand :=
      .starred { base := starBase, groups := starGroups ++ [{ name := "BSeal" }] }
    [admission model batches (countOf [fixedGroup (.relative 0) ["Seal2"], outGroup]),
      admission model out (countOf [sealAbsolute, outGroup]),
      admission outerKeyed out (countOf [sealAbsolute, outGroup]),
      admission model boxes (countOf [sealAbsolute, outGroup]),
      admission model batches (countOf [fixedGroup (.relative 0) ["Boxes", "BSeal"], outGroup]),
      admission model batches (countOf [fixedGroup (.relative 0) ["Seal2"]]),
      admission model batches (countOf [batchesGroup, outGroup]),
      admission model out (countOf [batchesGroup, outGroup]),
      admission outerKeyed out (countOf [batchesGroup, outGroup]),
      admission model batches (countOf [fixedGroup (.relative 0) ["Boxes"], outGroup]),
      admission model batches (countOf [fixedGroup (.relative 0) ["Seal2"], starredSeal])] =
    [contained, missingStar, noIndex, contained, contained, contained, contained, missingStar,
      noIndex, contained, contained] := by
  native_decide

/- An entity list's direct field is a plain read too: from the target's own group, where an
   undeclared declaring group defaults, it draws the missing-star class, and the index class exactly
   when its outermost level is index-keyed; a plain read beside a read of the target draws
   containment ahead of self-reference (`c-sum-none`, `i-c-none` on both keyed models, `f4c`). -/
example :
    let direct : AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.aggregate .sum
        { first := .field (absoluteField ["Probe", "Batches", "Boxes"] "Amt"), rest := [] }))
    let free := absoluteField ["Probe", "Out"] "Free"
    [admission model out direct, admission outerKeyed out direct, admission innerKeyed out direct,
      admission model batches
        (.binary .add (.atom (.numeric (.field free))) (.atom (.numeric (.field
          (relativeField [] "BW")))))] =
    [missingStar, noIndex, missingStar, contained] := by
  native_decide

/- The same list-wide gate answers a direct field and a fixed group read from the declaring group
   that binds their level, with containment. No row measures either on an entity list; they take
   the class a plain read and a group count's fixed operand draw there. -/
example :
    let sumOf (first : SurfaceFieldEntityOperand) : AuthoredNumericExpr SurfaceNumericComputationAtom :=
      .atom (.numeric (.aggregate .sum { first, rest := [rootW] }))
    [admission model batches (sumOf (.field (absoluteField ["Probe", "Batches"] "BW"))),
      admission model batches
        (sumOf (.group (.path { base := .absolute, groups := ["Probe", "Batches", "Seal2"] })))] =
    [contained, contained] := by
  native_decide

/-- `none` when admitted, otherwise the class the carried resolver error projects, for a String
    computation into the fixed `FreeS`. -/
private def stringAdmission (m : FlatModel) (declaringGroup : GroupPath)
    (e : StringExpr SurfaceFieldPath) : Option (Option KernelStaticDiagnostic) :=
  match elaborateStringComputationOperation m declaringGroup 13 e with
  | .ok _ => none
  | .error (.resolve error) => some error.diagnostic?
  | .error _ => some none

/- The String arm answers from the same table on a copy, a concatenation and `FieldValueAsString`,
   and ahead of target self-reference whichever side reads the target. -/
example :
    let bwAbsolute := absoluteField ["Probe", "Batches"] "BW"
    let concatenated := StringExpr.concat (.literal "x") (.field bText)
    let freeS := absoluteField ["Probe", "Out"] "FreeS"
    [stringAdmission model batches (.field bText),
      stringAdmission model out (.field bText),
      stringAdmission outerKeyed out (.field bText),
      stringAdmission model batches concatenated,
      stringAdmission model out concatenated,
      stringAdmission outerKeyed out concatenated,
      stringAdmission model batches (.fieldValueAsString bwAbsolute),
      stringAdmission model out (.fieldValueAsString bwAbsolute),
      stringAdmission outerKeyed out (.fieldValueAsString bwAbsolute),
      stringAdmission model batches (.field (relativeField ["Boxes"] "Name")),
      stringAdmission model batches (.concat (.field freeS) (.field bText)),
      stringAdmission model batches (.concat (.field bText) (.field freeS))] =
    [contained, missingStar, noIndex, contained, missingStar, noIndex, contained, missingStar,
      noIndex, contained, contained, contained] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.StarBinding
