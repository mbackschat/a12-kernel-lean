import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: a Custom `FirstFilledValue` at a join

`CA = FirstFilledValue(C1, C2)` feeds `CF = FirstFilledValue(CA, C3)` over one Custom type, read by
`NumberOfValueInFields("AA" In CA, C3)` and by two Number guards `KC = 1` under `FieldFilled(CF)` and
`KNC = 1` under `FieldNotFilled(CF)`, every reader authored ahead of what it reads. The fixture is the
model of the [Custom join grid](../../docs/sources/computation-scheduling-probes.md#src-extractor-join),
whose request registers the type with a maximum length of three, which the world's validator here
mirrors; every document row is the Kernel's, measured on both codegen strategies.

`CA` and `CF` are seeded with a value no row computes. The rows separate a fresh read of `CA` from its
seed (`r1`), a cleared `CA` that `CF` falls through from one it reads as poison (`r2`, `r3`),
exhaustion (`r4`), and a malformed third source `CF`'s scan never reaches though the count reads it
(`r5`).
-/

namespace A12Kernel.Conformance.ScalarComputationPlanCustom

open A12Kernel

private def code : CustomFieldTypeDeclaration := { name := "Code" }

private def names : List String := ["C1", "C2", "C3", "CA", "CF", "KC", "KNC", "VC"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  if name.startsWith "C" then
    { id := idOf name, groupPath := ["Xc"], name, policy := { kind := .string }, customType := some code }
  else
    { id := idOf name, groupPath := ["Xc"], name, policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := { fields := names.map declaration, timeZoneId := "Europe/Berlin" }

/-- The registered type's one constraint, a maximum length of three. -/
private def validator : RegisteredCustomFieldValidator := fun value _ =>
  if value.length > 3 then some { projectCode := "customFieldType.maxLength" } else none

private def world : World :=
  { now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == code.name then some validator else none }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def entities (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

private def one : DecodedNumericLiteral := { value := 1, authoredScale := 0 }

private def numberStep? (target : String) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateCompleteNumericTargetComputationTable model ["Xc"] (idOf target)
    [(guard, expression)]).toOption.map .number

private def firstFilled? (target first second : String) : Option (CheckedScalarComputationStep model) :=
  (checkCustomFirstFilledComputation model ["Xc"] (idOf target) (.list (entities first second))).toOption.map
    fun operation => .document (.ofCustomFirstFilled operation)

/-- The grid's computations in its authored order, every reader ahead of what it reads. -/
private def plan : CheckedScalarComputationPlan model :=
  let steps := ([numberStep? "KC" (some (.fieldFilled (idOf "CF"))) (.literal one),
    numberStep? "KNC" (some (.fieldNotFilled (idOf "CF"))) (.literal one),
    numberStep? "VC" none (.atom (.tokenValueCount "AA"
      { first := .field (.direct (bare "CA")), rest := [.field (.direct (bare "C3"))] })),
    firstFilled? "CF" "CA" "C3", firstFilled? "CA" "C1" "C2"].mapM id).get (by native_decide)
  (certifyScalarComputationPlan steps).toOption.get (by native_decide)

private def cell (name text : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path := [] }, stored := text
    raw := if name.startsWith "C" then .parsed (.str text) else
      match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
    numericDecimal := if name.startsWith "C" then none else text.toInt?.map ({ unscaled := ·, scale := 0 }) }

private def seeds : List (String × String) :=
  [("CA", "AAA"), ("CF", "AAA"), ("KC", "99"), ("KNC", "99"), ("VC", "99")]

private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.string (.accepted stored)) => some (target, stored.text)
  | .document target (.string .noValue) | .document target (.string (.poison _)) => some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.string (.errored _ _)) | .document _ (.dateTime _) | .document _ (.fullDate _)
  | .document _ (.time _) | .document _ (.enumeration _) | .document _ (.dateRange _)
  | .document _ (.boolean _) | .document _ (.dateFragment _) => none

/-- `CA`, `CF`, `KC`, `KNC` and `VC` over one document holding the given sources. -/
private def values? (sources : List (String × String)) : Option (List String) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := (seeds ++ sources).map fun (name, text) => cell name text }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  ["CA", "CF", "KC", "KNC", "VC"].mapM fun name => (found.find? (·.1 == idOf name)).map (·.2)

/- Rows `r1` and `r5`: `CF` reads the fresh `CA`, not its seed, and never reaches a malformed `C3`,
which the count reads and so clears. -/
example :
    values? [("C1", "AA"), ("C3", "A")] = some ["AA", "AA", "1", "-", "1"] ∧
    values? [("C1", "AA"), ("C3", "BBBB")] = some ["AA", "AA", "1", "-", "-"] := by
  native_decide

/- Rows `r2` to `r4`: a cleared `CA` lets `CF` fall through, a poisoned one ends `CF`'s scan and reaches
both guards and the count as poison, and exhaustion clears both targets. -/
example :
    values? [("C3", "A")] = some ["-", "A", "1", "-", "0"] ∧
    values? [("C1", "BBBB"), ("C3", "A")] = some ["-", "-", "-", "-", "-"] ∧
    values? [] = some ["-", "-", "-", "1", "0"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanCustom
