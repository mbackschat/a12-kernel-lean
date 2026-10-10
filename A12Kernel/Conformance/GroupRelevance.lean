import A12Kernel.Elaboration.CheckedIndexPreliminary

namespace A12Kernel.Conformance.GroupRelevance

open A12Kernel

private def parent : GroupPath := ["Form", "Parent"]
private def children : GroupPath := parent ++ ["Children"]
private def parts : GroupPath := children ++ ["Parts"]

private def model (capacity : Option Nat := some 2) : FlatModel :=
  { fields := [
      { id := 1, groupPath := children, name := "N", policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] },
      { id := 2, groupPath := children, name := "M", policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] },
      { id := 3, groupPath := parts, name := "K", policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10, 20] }]
    repeatableGroups := [
      { level := 10, path := children, repeatability := capacity },
      { level := 20, path := parts, repeatability := some 2 }] }

private def every (path : GroupPath) : RelevantEntityPattern :=
  { path, indices := path.map fun _ => .all }

private def child (coordinate : Nat) : RelevantEntityPattern :=
  { path := children, indices := [.concrete 1, .concrete 1, .concrete coordinate] }

private def field (name : String) (coordinate : Nat) : RelevantEntityPattern :=
  { path := children ++ [name], indices := [.all, .all, .concrete coordinate, .all] }

private def part (outer inner : Nat) (leaf : Bool) : RelevantEntityPattern :=
  { path := parts ++ if leaf then ["K"] else []
    indices := [.all, .all, .concrete outer, .concrete inner] ++ if leaf then [.all] else [] }

private def cells : List RelevantEntityPattern :=
  [1, 2].flatMap fun coordinate => [field "N" coordinate, field "M" coordinate]

private def nested (leaf : Bool) : List RelevantEntityPattern :=
  [1, 2].flatMap fun outer => [1, 2].map fun inner => part outer inner leaf

private def relevance (entities : List RelevantEntityPattern)
    (capacity : Option Nat := some 2) : A12Kernel.GroupRelevance :=
  (.partialSet entities : ValidationRelevanceScope).groupRelevance (model capacity) parent []

example : relevance [child 1, child 2] = .fullyRelevant := by native_decide
example : relevance [child 1] = .partlyRelevant := by native_decide
example : relevance [child 1, child 1] = .partlyRelevant := by native_decide
example : relevance [child 1, child 3] = .partlyRelevant := by native_decide
example : relevance [every children] = .fullyRelevant := by native_decide
example : relevance (cells ++ nested true) = .fullyRelevant := by native_decide
example : relevance (cells ++ nested false) = .fullyRelevant := by native_decide
example : relevance (cells ++ [part 1 1 true, part 2 2 true]) = .partlyRelevant := by native_decide
example : relevance [every (children ++ ["N"]), every parts] = .partlyRelevant := by native_decide
example : relevance [child 1] (some 1) = .fullyRelevant := by native_decide
example : relevance [child 1, child 2] none = .partlyRelevant := by native_decide
example : relevance [every children] none = .fullyRelevant := by native_decide
example : relevance [every children] (some 1999999999) = .fullyRelevant := by native_decide

private def boundModel : FlatModel :=
  { model (some 2) with
    fields := (model (some 2)).fields.map fun declaration =>
      { declaration with repeatableScope := 5 :: declaration.repeatableScope }
    repeatableGroups := { level := 5, path := parent, repeatability := some 2 } ::
      (model (some 2)).repeatableGroups }

private def boundChild (outer inner : Nat) : RelevantEntityPattern :=
  { path := children, indices := [.all, .concrete outer, .concrete inner] }

private def boundRelevance (entities : List RelevantEntityPattern) : A12Kernel.GroupRelevance :=
  (.partialSet entities : ValidationRelevanceScope).groupRelevance boundModel parent [(5, 1)]

example : boundRelevance [boundChild 1 1, boundChild 1 2] = .fullyRelevant := by native_decide
example : boundRelevance [boundChild 2 1, boundChild 2 2] = .noneRelevant := by native_decide
example : boundRelevance [boundChild 1 1, boundChild 2 2] = .partlyRelevant := by native_decide

private def state (entities : List RelevantEntityPattern) (data : DocumentData) :
    Option GroupPresenceState := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model (some 2))).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let view ← (checked.applyPartialGeneratedPreliminaryForScope (.partialSet entities)).toOption
  pure (← (view.groupPresenceInput parent [] false).toOption).derive

example : state [child 1, child 2] { instantiatedRows := [], cells := [] } =
    some ⟨false, false, .fullyRelevant⟩ := by native_decide
example : state [child 1] { instantiatedRows := [], cells := [] } =
    some ⟨false, false, .partlyRelevant⟩ := by native_decide
example : state [child 1, child 2]
    { instantiatedRows := [{ group := 10, path := [1] }], cells := [] } =
    some ⟨true, false, .fullyRelevant⟩ := by native_decide

end A12Kernel.Conformance.GroupRelevance
