import A12Kernel.Elaboration.NumericComputation.Core

/-! # Per-row star operands on a fixed-target computation

A star leaves the repeatable levels above its first star to be bound by its evaluation. On this arm
the target repeats at no level, so any such level is refused, and the Kernel's class is decided by
who binds the outermost one: the repeatable declaring group, nobody over an index-keyed group, or
nobody. A level left unstarred below the first star is refused with the missing-star class whatever
binds it. Every expected value is a `computation add --dry-run` verdict
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
        repeatableScope := [10, 11] }]
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

inductive Carrier where
  | sum | max | firstFilled | tokenCount | booleanCount | products | groupCount
  deriving Repr, DecidableEq

private def carriers : List Carrier :=
  [.sum, .max, .firstFilled, .tokenCount, .booleanCount, .products, .groupCount]

private def expression (shape : Shape) :
    Carrier → AuthoredNumericExpr SurfaceNumericComputationAtom
  | .sum => .atom (.numeric (.aggregate .sum (entity shape "Amt")))
  | .max => .atom (.numeric (.aggregate .maximum (entity shape "Amt")))
  | .firstFilled => .atom (.firstFilled (entity shape "Amt"))
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

end A12Kernel.Conformance.NumericComputation.StarBinding
