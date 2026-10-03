import A12Kernel.Elaboration.ComputationPredicate

namespace A12Kernel.Conformance.ComputationPredicate

private def model (kind : FieldKind) (repeated : Bool) : FlatModel := {
  fields := [
    { id := 1, name := "A", groupPath := ["Form", "Rows"], policy := { kind },
      repeatableScope := if repeated then [10] else [] },
    { id := 2, name := "B", groupPath := ["Form", "Rows"], policy := { kind },
      repeatableScope := if repeated then [10] else [] }]
  repeatableGroups := if repeated then [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] else [] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def numberSource : SurfaceComputationPredicate := .entityValueList {
  quantifier := .atLeastOne, fields := { first := .field (path "A"), rest := [] },
  values := { first := .field (path "B"), rest := [] } }

private def literalSource : SurfaceComputationPredicate := .tokenLiteralValueList {
  quantifier := .atLeastOne, fields := { first := .field (path "A"), rest := [] }, values := ["x"] }

private def number : FieldKind := .number { scale := 0, signed := true }

private def context (kind : FieldKind) (left right : RawCell) : ScalarComputationContext :=
  let read := fun id => formalCheck { kind } (if id == 1 then left else right)
  { read
    row := [(10, 1)]
    addressed := some {
      document := { rawCells := fun _ => none, instantiatedRows := [] }
      read := fun _ => read } }

private def run (kind : FieldKind) (repeated : Bool) (source : SurfaceComputationPredicate)
    (context : ScalarComputationContext) : Option ComputationConditionResult := do
  let checked ← ((model kind repeated).elaborateComputationPredicate ["Form"] ["Form", "Rows"] source).toOption
  (checked.evalChecked context).toOption

example : run number false numberSource (context number (.parsed (.num 3)) (.parsed (.num 3))) = some .holds ∧
    run number true numberSource (context number (.parsed (.num 3)) (.parsed (.num 3))) = some .holds := by
  native_decide

example : run .string false literalSource (context .string (.parsed (.str "x")) .empty) = some .holds ∧
    run .string false literalSource (context .string (.rejected .malformed) .empty) = some (.poison .malformed) := by
  native_decide

example : ((model number true).elaborateComputationPredicate ["Form"] ["Form"] numberSource).isOk = false := by
  native_decide

example : run number false numberSource { read := fun _ => formalCheck { kind := number } .empty } = some .notTrue := by
  native_decide

private def star (field : String) : SurfaceFieldEntitySource := {
  first := .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field }
  rest := [] }

private def starSource : SurfaceComputationPredicate := .entityValueList {
  quantifier := .atLeastOne, fields := star "A", values := star "B" }

example : run number true starSource { read := fun _ => formalCheck { kind := number } .empty } = none := by
  native_decide

private def memberValue (kind : FieldKind) (isMember : Bool) : RawCell :=
  match kind with
  | .number _ => .parsed (.num (if isMember then 7 else 3))
  | .string => .parsed (.str (if isMember then "member" else "other"))
  | _ => .empty

private def starredContext (kind : FieldKind) (secondRow : Bool) : ScalarComputationContext := {
  read := fun _ => formalCheck { kind } (.rejected .malformed)
  addressed := some {
    document := {
      rawCells := fun _ => none
      instantiatedRows := [{ group := 10, path := [1] }] ++
        if secondRow then [{ group := 10, path := [2] }] else [] }
    read := fun environment field =>
      let raw := if field == 1 then memberValue kind (environment.contains (10, 2))
        else if environment.contains (10, 1) then memberValue kind true else .empty
      formalCheck { kind } raw } }

example : run number true starSource (starredContext number true) = some .holds ∧
    run number true starSource (starredContext number false) = some .notTrue ∧
    run .string true starSource (starredContext .string true) = some .holds ∧
    run .string true starSource (starredContext .string false) = some .notTrue := by
  native_decide

private def footprint : Option (Bool × Bool × Bool × Bool) := do
  let checked ← ((model number true).elaborateComputationPredicate ["Form"] ["Form", "Rows"] numberSource).toOption
  pure (checked.referencesField 1, checked.referencesField 2, checked.rowBoundBool [], checked.rowBoundBool [10])

example : footprint = some (true, true, false, true) := by native_decide

end A12Kernel.Conformance.ComputationPredicate
