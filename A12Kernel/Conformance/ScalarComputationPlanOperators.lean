import A12Kernel.Elaboration.ScalarComputationRun

/-! # Authored scalar plan locks: operators and guards at a join

The second join grid of the authored scalar plan. Its joins read two Number producers through
subtraction, multiplication, `Max` and a rounded division, one join sits under a String gate, and
two copies are guarded by a computed target's fill state. The fixture is the model of the
[operator-join checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards),
and its eleven document rows are the Kernel's, measured on both codegen strategies.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanOperators

open A12Kernel

private def base1Id : FieldId := 0
private def base2Id : FieldId := 1
private def base3Id : FieldId := 2
private def gate1Id : FieldId := 3
private def gate2Id : FieldId := 4
private def p1Id : FieldId := 5
private def p2Id : FieldId := 6
private def subId : FieldId := 7
private def mulId : FieldId := 8
private def mxId : FieldId := 9
private def gId : FieldId := 10
private def hId : FieldId := 11
private def hnId : FieldId := 12
private def divId : FieldId := 13

private def numberDeclaration (id : FieldId) (name : String) (scale : Nat := 0) :
    FlatFieldDecl where
  id
  groupPath := ["Join"]
  name
  policy := { kind := .number { scale, signed := true } }

private def stringDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Join"]
  name
  policy := { kind := .string }

private def model : FlatModel :=
  { fields := [
      numberDeclaration base1Id "Base1", numberDeclaration base2Id "Base2",
      numberDeclaration base3Id "Base3",
      stringDeclaration gate1Id "Gate1", stringDeclaration gate2Id "Gate2",
      numberDeclaration p1Id "P1", numberDeclaration p2Id "P2",
      numberDeclaration subId "Sub", numberDeclaration mulId "Mul", numberDeclaration mxId "Mx",
      numberDeclaration gId "G", numberDeclaration hId "H", numberDeclaration hnId "HN",
      numberDeclaration divId "Div" 2] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberStep? (target : FieldId) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedScalarComputationStep model) := do
  let operation ← (elaborateNumericTargetComputationOperation
    model ["Join"] target expression).toOption
  let table ← (certifyNumericComputationTable
    [({ precondition := guard, operation } :
      ComputationAlternative (CheckedNumericTargetComputationOperation model))]).toOption
  pure (.number table)

private def read (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (bare field))

/-- The model's nine computations in its authored order: the joins ahead of their producers,
then the division authored after them. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? subId none (.binary .subtract (read "P1") (read "P2")),
    numberStep? mulId none (.binary .multiply (read "P1") (read "P2")),
    numberStep? mxId none
      (.extremumCall .maximum (.extremum .maximum (read "P1") (read "P2"))),
    numberStep? gId (some (.fieldFilled gate1Id)) (.binary .add (read "P1") (read "P2")),
    numberStep? hId (some (.fieldFilled p1Id)) (read "Base3"),
    numberStep? hnId (some (.fieldNotFilled p2Id)) (read "Base3"),
    numberStep? p1Id none (read "Base1"),
    numberStep? p2Id (some (.fieldFilled gate2Id)) (read "Base2"),
    numberStep? divId none
      (.round .halfUp ⟨2, by decide⟩ (.binary .divide (read "P1") (read "P2")))].mapM id).get
      (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

private def numberCell (field : FieldId) (amount : Int) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

private def malformedNumberCell (field : FieldId) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := "bad"
    raw := .rejected .malformed }

private def stringCell (field : FieldId) (stored : String) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.str stored) }

/-- Every computed target seeded with a value no row computes, so a stale read would show. -/
private def seeds : List ClassifiedCellInput :=
  [p1Id, p2Id, subId, mulId, mxId, gId, hId, hnId, divId].map (numberCell · 99)

private def reported : List FieldId :=
  [p1Id, p2Id, subId, mulId, mxId, gId, hId, hnId, divId]

/-- The amount with trailing fractional zeros dropped, the form the Kernel artifact prints. The
stored scale is not compared. -/
private def amount (stored : StoredNumber) : String :=
  let rec strip : Nat → Int → Nat → Int × Nat
    | 0, unscaled, scale => (unscaled, scale)
    | fuel + 1, unscaled, scale =>
        if scale > 0 && unscaled % 10 == 0 then strip fuel (unscaled / 10) (scale - 1)
        else (unscaled, scale)
  let (unscaled, scale) := strip stored.scale stored.unscaled stored.scale
  if scale == 0 then toString unscaled
  else
    let digits := toString unscaled.natAbs
    let padded := String.ofList (List.replicate (scale + 1 - min digits.length (scale + 1)) '0') ++
      digits
    let point := padded.length - scale
    (if unscaled < 0 then "-" else "") ++ (padded.take point).toString ++ "." ++
      (padded.drop point).toString

/-- A computed amount, `-` for a target the Kernel reports cleared without a formal error at it,
and `domain` for one it clears with its calculation-value error at the target. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, amount value)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .number target (.invalidNoValue .calculationValue) => some (target, "domain")
  | .number _ (.rejected _ _) | .string _ _ | .document _ _ => none

private def values? (cells : List ClassifiedCellInput) : Option (List String) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := seeds ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

private def inputs (base1 : Option ClassifiedCellInput := some (numberCell base1Id 7))
    (base2 : Option ClassifiedCellInput := some (numberCell base2Id 5))
    (base3 : Option ClassifiedCellInput := some (numberCell base3Id 2))
    (gate1 gate2 : Bool := true) : List ClassifiedCellInput :=
  [base1, base2, base3].filterMap id ++
    (if gate1 then [stringCell gate1Id "x"] else []) ++
    (if gate2 then [stringCell gate2Id "x"] else [])

/- Every source readable: each operator reads both fresh producers, the String gate holds, and the
   filled guard on the filled `P1` holds while the not-filled guard on the filled `P2` does not. -/
example :
    values? (inputs) = some ["7", "5", "2", "35", "7", "12", "2", "-", "1.4"] ∧
    values? (inputs (base1 := some (numberCell base1Id (-3)))) =
      some ["-3", "5", "-8", "-15", "5", "2", "2", "-", "-0.6"] ∧
    values? (inputs (gate1 := false)) = some ["7", "5", "2", "35", "7", "-", "2", "-", "1.4"] := by
  native_decide

/- A malformed producer poisons every operator's join, and a guard on the poisoned target is
   neither filled nor not filled: `H` and `HN` clear beside their own clean source. The other
   producer's guard still reads its own target. -/
example :
    values? (inputs (base1 := some (malformedNumberCell base1Id))) =
      some ["-", "5", "-", "-", "-", "-", "-", "-", "-"] ∧
    values? (inputs (base2 := some (malformedNumberCell base2Id))) =
      some ["7", "-", "-", "-", "-", "-", "2", "-", "-"] ∧
    values? (inputs (base1 := some (malformedNumberCell base1Id)) (gate2 := false)) =
      some ["-", "-", "-", "-", "-", "-", "-", "2", "-"] ∧
    values? (inputs (base3 := some (malformedNumberCell base3Id))) =
      some ["7", "5", "2", "35", "7", "12", "-", "-", "1.4"] := by
  native_decide

/- A producer cleared by its unmet gate reads as empty: every operator substitutes zero, `Max`
   included, so `Max(-3, empty)` is `0` rather than `-3`, and the division by that zero clears with
   the calculation-value error exactly as an explicit zero divisor does. The not-filled guard sees the
   fresh clear rather than the stale seed. An absent source copies as zero, which the filled guard
   reads as filled. -/
example :
    values? (inputs (gate2 := false)) = some ["7", "-", "7", "0", "7", "7", "2", "2", "domain"] ∧
    values? (inputs (base1 := some (numberCell base1Id (-3))) (gate2 := false)) =
      some ["-3", "-", "-3", "0", "0", "-3", "2", "2", "domain"] ∧
    values? (inputs (base2 := some (numberCell base2Id 0))) =
      some ["7", "0", "7", "0", "7", "7", "2", "-", "domain"] ∧
    values? (inputs (base1 := none)) = some ["0", "5", "-5", "0", "5", "5", "2", "-", "0"] := by
  native_decide

/-- A plan's certification: `.inl ()` when admitted, else the refusal and the class it draws. -/
private def planDecision? (steps : List (Option (CheckedScalarComputationStep model))) :
    Option (Unit ⊕ ScalarComputationPlanError × Option CalculationRefusal) := do
  let steps ← steps.mapM id
  match certifyScalarComputationPlan steps with
  | .ok _ => pure (.inl ())
  | .error cause => pure (.inr (cause, cause.calculationRefusal?))

/- The Kernel refuses a three-member circle and one closed through a precondition's read with the
   cycle class, as the plan does: a guard's read is an edge exactly as an operand's is. -/
example :
    planDecision? [numberStep? subId none (read "Mul"), numberStep? mulId none (read "Mx"),
        numberStep? mxId none (read "Sub")] =
      some (.inr (.cycle subId mulId, some .calcCycle)) ∧
    planDecision? [numberStep? hId (some (.fieldFilled gId)) (read "Base3"),
        numberStep? gId none (read "H")] =
      some (.inr (.cycle hId gId, some .calcCycle)) := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanOperators
