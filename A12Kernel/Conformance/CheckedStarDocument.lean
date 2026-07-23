import A12Kernel.Elaboration.CheckedStarDocument

/-! # Checked-document starred-field projection locks -/

namespace A12Kernel.Conformance.CheckedStarDocument

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10, 20] }

private def model : FlatModel :=
  { fields := [amount]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"],
        repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"],
        repeatability := some 2 }] }

private def segment (name : String) (starred : Bool := false) :
    SurfaceStarGroupSegment :=
  { name, starred }

private def source (outerStar : Bool := true) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      segment "Shop",
      segment "Sections" outerStar,
      segment "Items" true]
    field := "Amount" }

private def data : DocumentData :=
  { instantiatedRows := [
      { group := 20, path := [2, 1] },
      { group := 10, path := [2] },
      { group := 20, path := [1, 2] },
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [
      { address := { field := 7, path := [1, 1] }
        stored := "01"
        raw := .parsed (.num 1) },
      { address := { field := 7, path := [1, 2] }
        stored := ""
        raw := .presentEmpty }] }

private def world : World := { now := { epochMillis := 0 } }

private def checked? : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" data).toOption

private structure CellSnapshot where
  environment : Env
  address : CellAddr
  stored : Option String
  rawPresent : Bool
  observation : CellObservation
  deriving Repr, DecidableEq

private structure ProjectionSnapshot where
  hasOpenTail : Bool
  cells : List CellSnapshot
  deriving Repr, DecidableEq

private def snapshot : Option ProjectionSnapshot := do
  let checked ← checked?
  let path ← (elaborateStarFieldPath model amount.groupPath (source true)).toOption
  let resolved ← (path.resolveCheckedField checked []).toOption
  pure {
    hasOpenTail := resolved.topology.domain.hasOpenTail
    cells := resolved.cells.map fun entry => {
      environment := entry.environment
      address := entry.address
      stored := entry.stored
      rawPresent := entry.cell.rawPresent
      observation := observeCell .validation entry.cell
    }
  }

/- The checked projection preserves complete nested identity, canonical topology order, exact stored spelling, present-empty versus absent placement, and hierarchical tail state together. -/
example : snapshot = some {
    hasOpenTail := true
    cells := [
      { environment := [(10, 1), (20, 1)]
        address := { field := 7, path := [1, 1] }
        stored := some "01"
        rawPresent := true
        observation := .value (.num 1) },
      { environment := [(10, 1), (20, 2)]
        address := { field := 7, path := [1, 2] }
        stored := some ""
        rawPresent := true
        observation := .empty },
      { environment := [(10, 2), (20, 1)]
        address := { field := 7, path := [2, 1] }
        stored := none
        rawPresent := false
        observation := .empty }]
  } := by
  native_decide

private def overLimitModel : FlatModel :=
  { model with repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"],
        repeatability := some 1 },
      { level := 10, path := ["Shop", "Sections"],
        repeatability := some 2 }] }

private structure OverLimitSnapshot where
  hasOpenTail : Bool
  observations : List CellObservation
  deriving Repr, DecidableEq

private def overLimitSnapshot : Option OverLimitSnapshot := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      overLimitModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let path ←
    (elaborateStarFieldPath overLimitModel amount.groupPath (source true)).toOption
  let resolved ← (path.resolveCheckedField checked []).toOption
  pure {
    hasOpenTail := resolved.topology.domain.hasOpenTail
    observations := resolved.cells.map fun entry =>
      observeCell .validation entry.cell
  }

/- An actual over-limit row stays in canonical order as a formal cell and does not manufacture an omitted declared tail. -/
example : overLimitSnapshot = some {
    hasOpenTail := false
    observations := [
      .value (.num 1),
      .unknown .overRepetition,
      .empty]
  } := by
  native_decide

/- A missing fixed outer binding remains a structural addressing result and is never converted to a checked-cell UNKNOWN. -/
example : (do
    let checked ← checked?
    let path ← (elaborateStarFieldPath model amount.groupPath (source false)).toOption
    pure (match path.resolveCheckedField checked [] with
      | .error (.addressing (.missingBinding 10)) => true
      | _ => false)) = some true := by
  native_decide

end A12Kernel.Conformance.CheckedStarDocument
