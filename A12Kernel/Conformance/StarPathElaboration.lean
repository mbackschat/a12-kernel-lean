import A12Kernel.Elaboration.StarPath

/-! # Checked general star-path lowering locks -/

namespace A12Kernel.Conformance.StarPathElaboration

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Catalog", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 2, signed := false } }
    repeatableScope := [10, 20] }

private def sections : RepeatableGroupDecl :=
  { level := 10, path := ["Shop", "Catalog", "Sections"], repeatability := some 2 }

private def items : RepeatableGroupDecl :=
  { level := 20, path := ["Shop", "Catalog", "Sections", "Items"], repeatability := some 3 }

private def model : FlatModel :=
  { fields := [amount], repeatableGroups := [items, sections] }

private def segment (name : String) (starred : Bool := false) : SurfaceStarGroupSegment :=
  { name, starred }

private def relativeSource (outerStar innerStar : Bool) : SurfaceStarFieldPath :=
  { base := .relative 2
    groups := [segment "Sections" outerStar, segment "Items" innerStar]
    field := "Amount" }

private def absoluteSource (catalogStar outerStar innerStar : Bool) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [segment "Shop", segment "Catalog" catalogStar,
      segment "Sections" outerStar, segment "Items" innerStar]
    field := "Amount" }

private def resultOf (source : SurfaceStarFieldPath) (targetModel : FlatModel := model) :=
  match elaborateStarFieldPath targetModel amount.groupPath source with
  | .error _ => none
  | .ok checked => some (checked.declaration.id, checked.path)

private def errorOf (source : SurfaceStarFieldPath) (targetModel : FlatModel := model) :=
  match elaborateStarFieldPath targetModel amount.groupPath source with
  | .ok _ => none
  | .error error => some error

/- Parent navigation before a later star is legal, and the first starred repeatable axis owns reopening. -/
example :
    resultOf (relativeSource false true) = some (7,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 1 }) := by
  native_decide

/- Starring both nested repeatable groups reopens the whole ancestry. -/
example :
    resultOf (relativeSource true true) = some (7,
      { axes := [{ level := 10, repeatability := some 2 },
          { level := 20, repeatability := some 3 }], firstStar := 0 }) := by
  native_decide

/- A wildcard is legal only on a repeatable group, and every deeper repeatable axis after the first star must also be starred. -/
example :
    errorOf (absoluteSource true true true) =
      some (.wildcardOnNonrepeatable ["Shop", "Catalog"]) ∧
    errorOf (relativeSource true false) =
      some (.iterationBelowWildcard ["Shop", "Catalog", "Sections", "Items"]) ∧
    errorOf (relativeSource false false) = some (.missingWildcard amount.path) := by
  native_decide

/- Zero capacity is rejected by the shared topology invariant during checked lowering. -/
example :
    let zeroItems := { items with repeatability := some 0 }
    let zeroModel := { model with repeatableGroups := [zeroItems, sections] }
    errorOf (relativeSource false true) zeroModel =
      some (.addressing (.invalidRepeatability 20)) := by
  native_decide

end A12Kernel.Conformance.StarPathElaboration
