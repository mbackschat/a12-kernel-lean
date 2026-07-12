import A12Kernel.Elaboration.Flat

/-! # Checked flat-elaboration conformance locks -/

namespace A12Kernel.Conformance.Elaboration

open A12Kernel

private def numberInfo : NumField := { scale := 2, signed := false }

private def quantityDecl : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Quantity",
    policy := { kind := .number numberInfo } }

private def expressDecl : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "ExpressShipping",
    policy := { kind := .boolean } }

private def confirmDecl : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "TermsConfirmed",
    policy := { kind := .confirm } }

private def ancestorLimitDecl : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Limit",
    policy := { kind := .number { scale := 0, signed := true } } }

private def localLimitDecl : FlatFieldDecl :=
  { id := 4, groupPath := ["Order", "Details"], name := "Limit",
    policy := { kind := .number { scale := 1, signed := false } } }

private def externalCodeDecl : FlatFieldDecl :=
  { id := 5, groupPath := ["Reference"], name := "ExternalCode",
    policy := { kind := .boolean } }

private def repeatableCountDecl : FlatFieldDecl :=
  { id := 6, groupPath := ["Order", "Items"], name := "Count",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [quantityDecl, expressDecl, confirmDecl, ancestorLimitDecl,
      localLimitDecl, externalCodeDecl, repeatableCountDecl],
    fieldRefByShortNameAllowed := true }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def relative (parents : Nat) (groups : List String)
    (field : String) : SurfaceFieldPath :=
  { base := .relative parents, groups, field }

private def bare (field : String) : SurfaceFieldPath := relative 0 [] field

private def compare (op : SurfaceComparisonOp) (field : SurfaceFieldPath)
    (literal : SurfaceLiteral) : SurfaceCondition :=
  .compare op field literal

private def coreOf (result : Except ElabError (CheckedFlatCondition model)) :
    Option FlatCondition :=
  match result with
  | .ok checked => some checked.core
  | .error _ => none

private def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def resolvedIdOf (result : Except ResolveError FlatFieldDecl) : Option FieldId :=
  (valueOf result).map (·.id)

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) =
    some (.compare (.number .equal { id := 0, info := numberInfo } 0)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.compare (.boolean .equal { id := 1 } false)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some (.compare (.confirm .notEqual { id := 2 })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fieldNotFilled (.number { id := 0, info := numberInfo })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.and (.fieldFilled (absolute ["Order"] "ExpressShipping"))
      (compare .equal (absolute ["Order"] "Quantity") (.number 0)))) =
    some (.and (.fieldFilled (.boolean { id := 1 }))
      (.compare (.number .equal { id := 0, info := numberInfo } 0))) := by
  native_decide

-- Bare resolution is local-first, then nearest ancestor, then unique model-wide.
example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Limit")) = some 4 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Quantity")) = some 0 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "ExternalCode")) = some 5 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"]
    (relative 1 [] "Quantity")) = some 0 := by
  native_decide

example : errorOf (model.resolveField ["Order", "Details"]
    (relative 2 [] "Quantity")) = some (.aboveRoot 2) := by
  native_decide

private def ambiguousModel : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["One"], name := "Code", policy := { kind := .boolean } },
      { id := 1, groupPath := ["Two"], name := "Code", policy := { kind := .boolean } }],
    fieldRefByShortNameAllowed := true }

example : errorOf (ambiguousModel.resolveField ["Rule"] (bare "Code")) =
    some (.shortNameNotUnique "Code") := by
  native_decide

private def shortNamesDisabled : FlatModel :=
  { model with fieldRefByShortNameAllowed := false }

-- Local and ancestor tiers do not depend on the model-wide short-name flag.
example : resolvedIdOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "Quantity")) = some 0 := by
  native_decide

example : errorOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "ExternalCode")) = some (.invalidEntity (bare "ExternalCode")) := by
  native_decide

example : errorOf (model.resolveField ["Order"]
    (absolute ["Order"] "Missing")) =
    some (.invalidEntity (absolute ["Order"] "Missing")) := by
  native_decide

private def duplicateIdModel : FlatModel :=
  { fields := [quantityDecl, { expressDecl with id := 0 }] }

example : errorOf (elaborate duplicateIdModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateFieldId 0)) := by
  native_decide

private def duplicatePathModel : FlatModel :=
  { fields := [quantityDecl, { quantityDecl with id := 9 }] }

example : errorOf (elaborate duplicatePathModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateEntityPath ["Order", "Quantity"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order", "Items"] "Count"))) =
    some (.resolve (.repeatableReference ["Order", "Items", "Count"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.boolean true))) =
    some (.literalKindMismatch ["Order", "Quantity"] .number .boolean) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "TermsConfirmed") (.boolean false))) =
    some (.illegalConfirmLiteral ["Order", "TermsConfirmed"]) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "Quantity") (.number 10))) =
    some (.unsupportedOperator .less) := by
  native_decide

private def wrongKindRaw : RawFlatContext where
  read id := if id = 0 then .parsed (.bool true) else .empty

private def ordinaryRaw : RawFlatContext where
  read id :=
    if id = 0 then .parsed (.num 5)
    else if id = 1 then .parsed (.bool false)
    else if id = 2 then .parsed (.conf true)
    else .empty

example : valueOf (elaborateAndEvalFull model ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 5))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull model ["Order"] ordinaryRaw true
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.fired .value) := by
  native_decide

example : valueOf (elaborateAndEvalFull model ["Order"] ordinaryRaw true
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some .notFired := by
  native_decide

example : valueOf (elaborateAndEvalFull model ["Order"] { read := fun _ => .empty } false
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fired .omission) := by
  native_decide

-- Model-derived formal checking prevents an inconsistent runtime kind from entering eval.
example : valueOf (elaborateAndEvalFull model ["Order"] wrongKindRaw true
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide

-- Static success does not imply a definite runtime verdict: malformed data remains unknown.
example : (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.number 0))).isOk = true ∧
    valueOf (elaborateAndEvalFull model ["Order"] wrongKindRaw true
      (compare .equal (absolute ["Order"] "Quantity") (.number 0))) = some .unknown := by
  native_decide

end A12Kernel.Conformance.Elaboration
