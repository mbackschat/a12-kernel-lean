import A12Kernel.Elaboration.ScalarComputationRun

/-! # Authored scalar computation plan locks

A plan of any length runs its steps in dependency order, choosing the earliest authored step that
reads no other pending target. The fixture is the twelve-computation join model of the
[join checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-join-poison-and-substitution),
authored joins first, and its ten document rows are the Kernel's, measured on both codegen
strategies. Each row reports the computed value or, where the Kernel clears the target, `none`.
-/

namespace A12Kernel.Conformance.ScalarComputationPlan

open A12Kernel

private def base1Id : FieldId := 0
private def base2Id : FieldId := 1
private def base3Id : FieldId := 2
private def gate1Id : FieldId := 3
private def gate2Id : FieldId := 4
private def s1Id : FieldId := 5
private def s2Id : FieldId := 6
private def p1Id : FieldId := 7
private def p2Id : FieldId := 8
private def aId : FieldId := 9
private def bId : FieldId := 10
private def cId : FieldId := 11
private def finalId : FieldId := 12
private def final3Id : FieldId := 13
private def twiceId : FieldId := 14
private def saId : FieldId := 15
private def sbId : FieldId := 16
private def sFinalId : FieldId := 17
private def nsId : FieldId := 18

private def numberDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Join"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def stringDeclaration (id : FieldId) (name : String)
    (maxLength : Option Nat := some 20) (digits : Bool := false) : FlatFieldDecl where
  id
  groupPath := ["Join"]
  name
  policy := { kind := .string }
  stringPolicy := { maxLength }
  stringPatternSource := if digits then some "[0-9]+" else none

private def model : FlatModel :=
  { fields := [
      numberDeclaration base1Id "Base1", numberDeclaration base2Id "Base2",
      numberDeclaration base3Id "Base3",
      stringDeclaration gate1Id "Gate1" none, stringDeclaration gate2Id "Gate2" none,
      stringDeclaration s1Id "S1" (some 6) true, stringDeclaration s2Id "S2" (some 6) true,
      numberDeclaration p1Id "P1", numberDeclaration p2Id "P2",
      numberDeclaration aId "A", numberDeclaration bId "B", numberDeclaration cId "C",
      numberDeclaration finalId "Final", numberDeclaration final3Id "Final3",
      numberDeclaration twiceId "Twice",
      stringDeclaration saId "SA", stringDeclaration sbId "SB",
      stringDeclaration sFinalId "SFinal", stringDeclaration nsId "NS"] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def stringStep? (target : FieldId) (expression : StringExpr SurfaceFieldPath) :
    Option (CheckedScalarComputationStep model) := do
  let operation ← (elaborateStringComputationOperation model ["Join"] target expression).toOption
  let table ← (certifyStringComputationTable
    [({ precondition := none, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))]).toOption
  pure (.string table)

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

private def plus (left right : AuthoredNumericExpr SurfaceNumericAtom) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add left right

/-- The model's twelve computations in its authored order, every join ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? finalId none (plus (read "A") (read "B")),
    numberStep? final3Id none (plus (plus (read "A") (read "B")) (read "C")),
    numberStep? twiceId none (plus (read "P1") (read "P1")),
    stringStep? sFinalId (.concat (.field (bare "SA")) (.field (bare "SB"))),
    stringStep? nsId (.concat (.fieldValueAsString (bare "A")) (.field (bare "SB"))),
    numberStep? aId none (read "P1"),
    numberStep? bId none (read "P2"),
    stringStep? saId (.field (bare "S1")),
    stringStep? sbId (.field (bare "S2")),
    numberStep? cId none (read "Base3"),
    numberStep? p1Id (some (.fieldFilled gate1Id)) (read "Base1"),
    numberStep? p2Id (some (.fieldFilled gate2Id)) (read "Base2")].mapM id).get
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

/-- Every computed target seeded with a value no row computes, as the Kernel rows are, so a stale
read would show. -/
private def seeds : List ClassifiedCellInput :=
  [p1Id, p2Id, aId, bId, cId, finalId, final3Id, twiceId].map (numberCell · 99) ++
    [saId, sbId, sFinalId, nsId].map (stringCell · "99")

private def reported : List FieldId :=
  [p1Id, p2Id, aId, bId, cId, finalId, final3Id, twiceId, saId, sbId, sFinalId, nsId]

/-- A computed value, `none` for a cleared target, or no projection for an errored one, which no
Kernel row reports: every target the grid clears is reported not errored. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × Option String)
  | .number target (.accepted value) => some (target, some (toString value.unscaled))
  | .string target (.accepted term) => some (target, some term.text)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, none)
  | .string target .noValue | .string target (.poison _) => some (target, none)
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ (.errored _ _)
  | .document _ _ => none

/-- The computed value of each reported target, `none` where it is cleared. -/
private def values? (cells : List ClassifiedCellInput) : Option (List (Option String)) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := seeds ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

private def cleanInputs (without : List FieldId := []) : List ClassifiedCellInput :=
  ([numberCell base1Id 7, numberCell base2Id 5, numberCell base3Id 2,
    stringCell gate1Id "g", stringCell gate2Id "g",
    stringCell s1Id "12", stringCell s2Id "34"]).filter
      fun cell => !without.contains cell.address.field

/- Every source readable: the joins read every fresh completion rather than a seed, and the String
   and Number-to-String joins concatenate in authored operand order. -/
example :
    values? (cleanInputs) =
      some [some "7", some "5", some "7", some "5", some "2", some "12", some "14", some "14",
        some "12", some "34", some "1234", some "734"] := by
  native_decide

/- A malformed producer poisons every Number join that reaches it, whatever the other branch holds:
   a second malformed producer, a producer cleared by its unmet precondition, which reads as zero,
   or an absent source, which substitutes zero. The independent `C`, `SA` and `SB` still compute. -/
example :
    values? (malformedNumberCell base1Id :: malformedNumberCell base2Id ::
        cleanInputs [base1Id, base2Id]) =
      some [none, none, none, none, some "2", none, none, none,
        some "12", some "34", some "1234", none] ∧
    values? (malformedNumberCell base1Id :: cleanInputs [base1Id, gate2Id]) =
      some [none, none, none, some "0", some "2", none, none, none,
        some "12", some "34", some "1234", none] ∧
    values? (malformedNumberCell base1Id :: cleanInputs [base1Id, base2Id]) =
      some [none, some "0", none, some "0", some "2", none, none, none,
        some "12", some "34", some "1234", none] := by
  native_decide

/- Two producers cleared by their unmet preconditions read as empty, so every join substitutes
   zero and the Number-to-String join renders it. A malformed third operand of a three-operand join
   clears that join alone. -/
example :
    values? (cleanInputs [gate1Id, gate2Id]) =
      some [none, none, some "0", some "0", some "2", some "0", some "2", some "0",
        some "12", some "34", some "1234", some "034"] ∧
    values? (malformedNumberCell base3Id :: cleanInputs [base3Id]) =
      some [some "7", some "5", some "7", some "5", none, some "12", none, some "14",
        some "12", some "34", some "1234", some "734"] := by
  native_decide

/- The String join follows the same split: a pattern-refused source poisons its copy and the join,
   while an absent one clears its copy, which the join reads as empty text. Both absent leave the
   join empty, so it clears too. An absent Number producer substitutes zero through the mixed join. -/
example :
    values? (stringCell s1Id "x1" :: cleanInputs [s1Id]) =
      some [some "7", some "5", some "7", some "5", some "2", some "12", some "14", some "14",
        none, some "34", none, some "734"] ∧
    values? (cleanInputs [s1Id, s2Id]) =
      some [some "7", some "5", some "7", some "5", some "2", some "12", some "14", some "14",
        none, none, none, some "7"] ∧
    values? (cleanInputs [s1Id]) =
      some [some "7", some "5", some "7", some "5", some "2", some "12", some "14", some "14",
        none, some "34", some "34", some "734"] ∧
    values? (cleanInputs [base1Id]) =
      some [some "0", some "5", some "0", some "5", some "2", some "5", some "7", some "0",
        some "12", some "34", some "1234", some "034"] := by
  native_decide

/- The plan runs the earliest authored step that reads no other pending target, so an independent
   step keeps its authored place among the ready ones and every join waits for its last producer.
   The Kernel's own order among independent steps is unmeasured; the rows fix only dependency
   order. -/
example :
    plan.executionTargetFields =
      [saId, sbId, sFinalId, cId, p1Id, twiceId, aId, nsId, p2Id, bId, finalId, final3Id] ∧
    plan.authoredTargetFields =
      [finalId, final3Id, twiceId, sFinalId, nsId, aId, bId, saId, sbId, cId, p1Id, p2Id] := by
  native_decide

/-- A plan's certification: `.inl ()` when admitted, else the refusal and the class it draws. -/
private def planDecision? (steps : List (Option (CheckedScalarComputationStep model))) :
    Option (Unit ⊕ ScalarComputationPlanError × Option CalculationRefusal) := do
  let steps ← steps.mapM id
  match certifyScalarComputationPlan steps with
  | .ok _ => pure (.inl ())
  | .error cause => pure (.inr (cause, cause.calculationRefusal?))

/- A cycle is refused with the Kernel's cycle class, and so is a plan where a step waits on one,
   since the Kernel sorts the whole model's computed fields before it generates anything
   ([`spec/09`](../../spec/09-computations.md) §1), measured on two- and three-member circles at the
   [operator-join checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards).
   The waiting plan's refusal names the waiting step `C`, which lies off the cycle. The acyclic control is
   admitted. -/
example :
    planDecision? [numberStep? aId none (read "B"), numberStep? bId none (read "A")] =
      some (.inr (.cycle aId bId, some .calcCycle)) ∧
    planDecision? [numberStep? cId none (read "A"), numberStep? aId none (read "B"),
        numberStep? bId none (read "A")] =
      some (.inr (.cycle cId aId, some .calcCycle)) ∧
    planDecision? [numberStep? aId none (read "B"), numberStep? bId none (read "Base2")] =
      some (.inl ()) := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlan
