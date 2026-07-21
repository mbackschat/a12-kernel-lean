import A12Kernel.Elaboration.NumericAggregate

/-! # Checked nonrepeatable Number aggregate lowering locks -/

namespace A12Kernel.Conformance.NumericAggregateElaboration

open A12Kernel

private def unsignedA : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "UnsignedA",
    policy := { kind := .number { scale := 0, signed := false } } }

private def signedB : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "SignedB",
    policy := { kind := .number { scale := 0, signed := true } } }

private def unsignedC : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "UnsignedC",
    policy := { kind := .number { scale := 0, signed := false } } }

private def text : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Text",
    policy := { kind := .string } }

private def repeated : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [unsignedA, signedB, unsignedC, text, repeated]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def sum (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath) : SurfaceNumericAggregateFields :=
  { first, rest }

private def raw (a b c : RawCell) : RawFlatContext where
  read field :=
    if field = unsignedA.id then a
    else if field = signedB.id then b
    else if field = unsignedC.id then c
    else .empty

private def operandOf (authored : SurfaceNumericAggregateFields)
    (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateSum input)

private def extremumOperandOf (op : NumericExtremumOp)
    (authored : SurfaceNumericAggregateFields) (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateExtremum op input)

private def errorOf (authored : SurfaceNumericAggregateFields) : Option NumericAggregateElabError :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def tenPow50 : Rat := 10 ^ 50

/- Authored field order reaches the existing staged precision-50 sum unchanged. -/
example :
    operandOf
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
          (.parsed (.num (3 / 5)))) =
        some (.value (3 / 5) .fixed) ∧
      operandOf
        (sum (bare "SignedB") [bare "UnsignedC", bare "UnsignedA"])
        (raw (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
          (.parsed (.num (3 / 5)))) =
        some (.value 1 .fixed) := by
  native_decide

/- Missing direction comes from the missing declaration, not a representative present field. -/
example :
    operandOf (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num 7)) .presentEmpty .empty) =
        some (.value 7 .both) ∧
      operandOf (sum (bare "SignedB") [bare "UnsignedA"])
        (raw .presentEmpty (.parsed (.num 7)) .empty) =
        some (.value 7 .growOnly) := by
  native_decide

/- A source-level nonempty all-empty list has the aggregate's fillable zero identity. -/
example :
    operandOf (sum (bare "UnsignedA") [bare "SignedB"])
      (raw .empty .presentEmpty .empty) = some (.value 0 .both) := by
  native_decide

/- Raw input is classified with the same model and the first unavailable source wins. -/
example :
    operandOf
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num 7)) (.rejected .declaredConstraint)
          (.rejected .malformed)) =
      some (.unknown .declaredConstraint) := by
  native_decide

/- Wrong declared kinds and repeatable sources fail before a resolved side exists. -/
example :
    errorOf (sum (bare "Text") []) =
        some (.fieldKindMismatch text.path .string) ∧
      errorOf (sum (absolute ["Form", "Rows"] "Amount") []) =
        some (.resolve (.repeatableReference repeated.path)) := by
  native_decide

/- Direct nonrepeatable extrema drop empty cells without substituting zero and retain their operator-specific missing direction. -/
example :
    extremumOperandOf .maximum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num (-5))) .presentEmpty .empty) =
        some (.value (-5) .growOnly) ∧
      extremumOperandOf .minimum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num 5)) .presentEmpty .empty) =
        some (.value 5 .shrinkOnly) := by
  native_decide

/- The shared checked field-list boundary preserves the extrema all-empty identity and first-unavailable cause. -/
example :
    extremumOperandOf .maximum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw .empty .presentEmpty .empty) =
        some (.value 0 .both) ∧
      extremumOperandOf .minimum
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num 7)) (.rejected .declaredConstraint)
          (.rejected .malformed)) =
        some (.unknown .declaredConstraint) := by
  native_decide

end A12Kernel.Conformance.NumericAggregateElaboration
