import A12Kernel.Elaboration.NumericSource

/-! # A12Kernel.Conformance.NumericCompositionAdmission — composition runs one way

Two numeric operations can each contain the other syntactically, so which nesting the Kernel admits
is not derivable from either operator's own rule. The measurement settles it in one direction only:
a wrapper or an extremum **contains** an aggregate, while an aggregate's operand list contains no
expression of any kind ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-aggregate-operand-list-takes-paths-only),
seven `KERNEL_CONFIRMED` rows).

These cases lock the admitting half. The refusing half — `Sum(Abs([G/Base]))`, `MVK_UNEXPECTED_TOKEN`
— needs no case because it is **unrepresentable rather than rejected**: an aggregate's source is
`SurfaceNumericAggregateFields`, whose `first` and `rest` are `SurfaceFieldPath`, so no expression
can be written into that position at all. That is the stronger guarantee, and stating it here is
what keeps a later widening of that field from silently crossing a measured Kernel refusal.

Static admission only, matching the evidence: every retained row is a `computation add --dry-run`,
so nothing here bears on evaluation, scale, or the target comparison.
-/

namespace A12Kernel.Conformance.NumericCompositionAdmission

open A12Kernel

private abbrev Expr := AuthoredNumericExpr SurfaceNumericAtom

private def path (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def field : Expr := .atom (.field (path "F"))

/-- `Sum(G*/Base)` stands in for the measured aggregate. Which aggregate operation it carries is not
    what these rows separate — the gate reads the node as an atom — so one representative is used. -/
private def aggregate : Expr :=
  .atom (.aggregate .sum { first := path "Base", rest := [path "Alt"] })

private def admits (expression : Expr) : Bool :=
  expression.isAdmittedResolvedNumericOperation

/-- One authored `Min`/`Max` call over two operands, which is `extremumCall` wrapping the
    left-associated internal fold rather than a bare `extremum` node. Spelled once here because the
    bare node is **never** admitted on its own, and writing it directly is the natural mistake. -/
private def extremumOf (left right : Expr) : Expr :=
  .extremumCall .minimum (.extremum .minimum left right)

/- **`Abs` nests, and the admitted depth is not one.** Depths one through three are the measured
   rows. The gate carries no depth bound at all, so five is admitted too — recorded as the estate's
   own behavior rather than as a Kernel claim, since the checkpoint searched for no bound and says
   so. A future measurement finding a Kernel limit would land here as a red row. -/
example :
    admits (.abs field) = true ∧
      admits (.abs (.abs field)) = true ∧
      admits (.abs (.abs (.abs field))) = true ∧
      admits (.abs (.abs (.abs (.abs (.abs field))))) = true := by
  native_decide

/- **An aggregate composes inside a wrapper and inside an extremum**, which is the measured half of
   the one-way rule. The extremum rows run the aggregate in **both** operand positions: the fold is
   left-associated, so an operand rule that read only the leading position would pass one order and
   fail the other, and one order alone cannot tell the two apart. -/
example :
    admits (.abs aggregate) = true ∧
      admits (extremumOf aggregate field) = true ∧
      admits (extremumOf field aggregate) = true ∧
      admits (extremumOf (.abs aggregate) field) = true := by
  native_decide

/- The checkpoint's own control, kept because it is what makes the rows above informative: a plain
   arithmetic expression is admitted through the identical gate, so no admission above is the gate
   being absent for this shape. -/
example : admits (.binary .multiply field (.literal { value := 2, authoredScale := 0 })) = true := by
  native_decide

/- **The gate is not vacuous**, which no positive row can establish. An immediate literal directly
   under a wrapper stays refused, and so does a bare `extremum` node outside its call — the two
   things this gate actually rejects. Without these, a gate returning `true` everywhere would
   satisfy every row above. -/
example :
    admits (.abs (.literal { value := 2, authoredScale := 0 })) = false ∧
      admits (.extremum .minimum aggregate field) = false := by
  native_decide

end A12Kernel.Conformance.NumericCompositionAdmission
