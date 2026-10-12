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

private def suffixModel : FlatModel := {
  fields := [{
    id := 1, name := "N", groupPath := parts ++ ["Detail"],
    repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := (model (some 2)).repeatableGroups }

private def suffixScope (groupCoordinate fieldCoordinate : RelevanceIndex) : ValidationRelevanceScope :=
  .partialSet [{
    path := parts ++ ["Detail", "N"],
    indices := [.all, .all, .all, .all, groupCoordinate, fieldCoordinate] }]

example : (suffixScope (.concrete 1) (.concrete 2)).groupRelevance suffixModel parent [] =
    .fullyRelevant := by native_decide

example : (suffixScope (.concrete 2) .all).groupRelevance suffixModel parent [] =
    .partlyRelevant := by native_decide

example : (suffixScope (.concrete 1) (.concrete 2)).coversCell suffixModel
    (parts ++ ["Detail", "N"]) [(10, 1), (20, 1)] = false ∧
    ((suffixScope (.concrete 1) (.concrete 2)).coversDeclaredFieldExtent suffixModel
      (parts ++ ["Detail", "N"]) [10, 20] []).toOption = some false := by native_decide

private def productParents : GroupPath := ["Form", "Parents"]
private def productGroup : GroupPath := productParents ++ ["Group"]
private def productA : GroupPath := productGroup ++ ["A"]
private def productB : GroupPath := productA ++ ["B"]
private def productC : GroupPath := productB ++ ["C"]

private def productModel (capacity : Option Nat := some 2) : FlatModel := {
  fields := [{
    id := 1, name := "N", groupPath := productC ++ ["Detail"],
    repeatableScope := [1, 10, 20, 30],
    policy := { kind := .number { scale := 0, signed := false } } }]
  repeatableGroups := [
    { level := 1, path := productParents, repeatability := some 2 },
    { level := 10, path := productA, repeatability := capacity },
    { level := 20, path := productB, repeatability := capacity },
    { level := 30, path := productC, repeatability := capacity }] }

private def productSelector (outer : Nat) (a b c : RelevanceIndex) : RelevantEntityPattern :=
  { path := productC ++ ["Detail", "N"],
    indices := [.concrete 1, .concrete outer, .concrete 1, a, b, c, .concrete 1, .all] }

private def productCell (outer a b c : Nat) : RelevantEntityPattern :=
  productSelector outer (.concrete a) (.concrete b) (.concrete c)

private def completeProduct (outer : Nat) : List RelevantEntityPattern :=
  [1, 2].flatMap fun a => [1, 2].flatMap fun b => [1, 2].map fun c =>
    productCell outer a b c

private def productDiagonal (outer : Nat) : List RelevantEntityPattern :=
  [productCell outer 1 1 1, productCell outer 2 2 2]

private def productRelevance (entities : List RelevantEntityPattern) (outer : Nat := 1)
    (capacity : Option Nat := some 2) : A12Kernel.GroupRelevance :=
  (.partialSet entities : ValidationRelevanceScope).groupRelevance
    (productModel capacity) productGroup [(1, outer)]

example : productRelevance (completeProduct 1) = .fullyRelevant := by native_decide
example : productRelevance (completeProduct 2) 2 = .fullyRelevant := by native_decide
example : productRelevance (productDiagonal 1) = .partlyRelevant := by native_decide
example : productRelevance (productDiagonal 1 ++ productDiagonal 1) =
    .partlyRelevant := by native_decide
example : productRelevance ((completeProduct 1).drop 1) = .partlyRelevant := by native_decide
example : productRelevance ((completeProduct 1).drop 1 ++ [productCell 1 3 1 1]) =
    .partlyRelevant := by native_decide
example : productRelevance ((completeProduct 1).drop 1 ++ [productCell 2 1 1 1]) =
    .partlyRelevant := by native_decide
example : productRelevance (completeProduct 2) = .noneRelevant := by native_decide
example : productRelevance (completeProduct 1) 2 = .noneRelevant := by native_decide
example : productRelevance (completeProduct 1 ++ completeProduct 1) =
    .fullyRelevant := by native_decide
example : productRelevance [productSelector 1 .all .all .all] =
    .fullyRelevant := by native_decide
example : productRelevance (completeProduct 1) 1 none = .partlyRelevant := by native_decide
example : productRelevance [productSelector 1 .all .all .all] 1 none =
    .fullyRelevant := by native_decide

private def productAbsence (entities : List RelevantEntityPattern) (outer : Nat := 1)
    (capacity : Option Nat := some 2) : Option GroupPresenceState := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (productModel capacity)).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 1, path := [1] }, { group := 1, path := [2] }],
    cells := [] }).toOption
  let view ← (checked.applyPartialGeneratedPreliminaryForScope (.partialSet entities)).toOption
  pure (← (view.groupPresenceInput productGroup [(1, outer)] false).toOption).derive

example : productAbsence (completeProduct 1) =
    some ⟨false, false, .fullyRelevant⟩ := by native_decide
example : productAbsence (productDiagonal 1) =
    some ⟨false, false, .partlyRelevant⟩ := by native_decide
example : productAbsence (completeProduct 2) =
    some ⟨false, false, .noneRelevant⟩ := by native_decide
example : productAbsence (completeProduct 2) 2 =
    some ⟨false, false, .fullyRelevant⟩ := by native_decide
example : productRelevance [productSelector 1 .all .all .all] 1 (some 1999999999) =
    .fullyRelevant := by native_decide
example : productAbsence [productSelector 1 .all .all .all] 1 (some 1999999999) =
    some ⟨false, false, .fullyRelevant⟩ := by native_decide

end A12Kernel.Conformance.GroupRelevance
