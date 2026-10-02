import A12Kernel.Elaboration.ScalarComputationRunResult
import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored scalar plan locks: a typed `FirstFilledValue` star leaves an over-limit row out

At a root `Rg`, `FS = FirstFilledValue(Rows*/Tag)`, `FB = FirstFilledValue(Rows*/Flag)`,
`FD = FirstFilledValue(Rows*/Day)` and `FE = FirstFilledValue(Rows*/Code)` scan a repeatable `Rows` of
at most two rows over a String, a Boolean, a full Date and an Enumeration, each read by a Number guard
`K = 1` under `FieldNotFilled` of its scan, the guards authored ahead of the scans. Beside them the
Number `FN = FirstFilledValue(Rows*/Num Having [Rows/Gate] > 0)` runs as a fixed table of the
repeatable plan, the route a Number star scan takes; Lean filters by `FieldFilled(Rows/Gate)`, which
keeps the same rows on every document here, since a `Gate` is either absent or `1`. Every target is seeded with a value no row computes. The documents
are the Kernel's rows of the [typed-scan capacity grid](../../evidence/kernel-30.8.1/captures/first-filled-capacity-2026-10-02/),
measured on both codegen strategies.

The guards are the separator: a scan whose only filled row is over the limit clears its target, as
exhaustion does, and every guard then computes, so the row was left out rather than read as poison;
a malformed in-capacity `Day` clears its guard, which shows a poisoned scan does reach it. `FN`
separates on its own value: exhausted it reads `0`, and poisoned it clears.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanFirstFilledCapacity

open A12Kernel

private def rowsPath : GroupPath := ["Rg", "Rows"]

private def names : List String :=
  ["FS", "FB", "FD", "KS", "KB", "KD", "FE", "KE", "FN", "Tag", "Flag", "Day", "Code", "Num", "Gate"]

private def rowFields : List String := ["Tag", "Flag", "Day", "Code", "Num", "Gate"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let base : FlatFieldDecl := if rowFields.contains name then
      { id := idOf name, groupPath := rowsPath, name, repeatableScope := [10], policy := { kind := .string } }
    else { id := idOf name, groupPath := ["Rg"], name, policy := { kind := .string } }
  match name with
  | "FB" | "Flag" => { base with policy := { kind := .boolean } }
  | "FD" | "Day" => { base with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }
  | "FE" | "Code" => { base with
      policy := { kind := .enumeration }, enumeration := some { storedTokens := ["A", "B"] } }
  | "KS" | "KB" | "KD" | "KE" | "FN" | "Num" | "Gate" =>
      { base with policy := { kind := .number { scale := 0, signed := true } } }
  | _ => base

private def model : FlatModel :=
  { fields := names.map declaration
    repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 2 }]
    timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def rowsStarPath (field : String) : SurfaceStarFieldPath :=
  { base := .relative 0, groups := [{ name := "Rows", starred := true }], field }

private def rowsStar (field : String) : SurfaceFirstFilledSource := .star (rowsStarPath field)

private def one : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 1, authoredScale := 0 }

private def guardStep? (target scanned : String) : Option (CheckedScalarComputationStep model) :=
  (elaborateNumericTargetComputationTable model ["Rg"] (idOf target)
    [(some (.fieldNotFilled (idOf scanned)), one)]).toOption.map .number

/-- The grid's computations in its authored order, the guards ahead of the scans they read. -/
private def plan : CheckedScalarComputationPlan model :=
  let steps := ([guardStep? "KS" "FS", guardStep? "KB" "FB", guardStep? "KD" "FD", guardStep? "KE" "FE",
    (checkStringFirstFilledComputation model ["Rg"] (idOf "FS") ⟨.star (rowsStarPath "Tag"), []⟩).toOption.map
      fun operation => .document (.ofStringFirstFilled operation),
    (checkBooleanFirstFilledComputation model ["Rg"] (idOf "FB") (rowsStar "Flag")).toOption.map
      fun operation => .document (.ofBooleanFirstFilled operation),
    (checkFullDateFirstFilledComputation model ["Rg"] (idOf "FD") (rowsStar "Day")).toOption.map
      fun operation => .document (.ofFullDateFirstFilled operation),
    (elaborateEnumerationFirstFilledComputation model ["Rg"] (idOf "FE")
      { first := .star (rowsStarPath "Code"), rest := [] }).toOption.map
      fun operation => .document (.ofEnumerationFirstFilled operation)].mapM id).get (by native_decide)
  (certifyScalarComputationPlan steps).toOption.get (by native_decide)

/-- `FN` as the repeatable plan's one fixed table. -/
private def numberPlan : CheckedRepeatableNumberPlan model :=
  let gated : SurfaceCorrelatedHaving := .presence .filled
    { origin := .inner, field := { base := .relative 0, groups := ["Rows"], field := "Gate" } }
  let table := (elaborateCompleteNumericTargetComputationTable model ["Rg"] (idOf "FN")
    [(none, .atom (.firstFilled { first := .starHaving (rowsStarPath "Num") gated, rest := [] }))]).toOption.get
      (by native_decide)
  (certifyRepeatableNumberPlan [table]).toOption.get (by native_decide)

private def classified (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match declaration.policy.kind with
  | .boolean => classifyStoredBooleanText text
  | .number _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
  | .enumeration => .parsed (.enum text)
  | .temporal _ _ => match certifyFullDateInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD
          (.rejected .dateFormat)
      | .error _ => .rejected .dateFormat
  | _ => .parsed (.str text)

private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  let declaration := declaration name
  { address := { field := declaration.id, path }, stored := text, raw := classified declaration text
    numericDecimal := if ["KS", "KB", "KD", "KE", "FN", "Num", "Gate"].contains name then
      text.toInt?.map ({ unscaled := ·, scale := 0 }) else none }

private def seeds : List (String × String) :=
  [("FS", "zz"), ("FB", "false"), ("FD", "1999-09-09"), ("KS", "99"), ("KB", "99"), ("KD", "99"),
    ("FE", "B"), ("KE", "99"), ("FN", "99")]

private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.string (.accepted stored)) => some (target, stored.text)
  | .document target (.boolean (.value value)) => some (target, toString value)
  | .document target (.fullDate (.accepted stored)) => some (target, stored.text)
  | .document target (.enumeration (.accepted stored)) => some (target, stored.text)
  | .document target (.enumeration .noValue) | .document target (.enumeration (.poison _))
  | .document target (.string .noValue) | .document target (.string (.poison _))
  | .document target (.boolean .noValue) | .document target (.boolean (.poison _))
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _)) =>
      some (target, "-")
  | _ => none

/-- `FS`, `FB`, `FD`, `FE`, `KS`, `KB`, `KD`, `KE` and `FN` over one document whose `Rows` rows hold
the given `Tag`, `Flag`, `Day`, `Code`, `Num` and `Gate` texts, `[]` for an instantiated row holding no
cell. -/
private def values? (rows : List (List String)) : Option (List String) := do
  let rowCells := rows.zipIdx.flatMap fun (texts, index) =>
    (rowFields.zip texts).map fun (name, text) => cell name [index + 1] text
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := rows.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
      cells := seeds.map (fun (name, text) => cell name [] text) ++ rowCells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let numbers ← (numberPlan.execute world input).toOption
  let found := (← outcomes.mapM valueOf?) ++ (← numbers.mapM fun outcome => match outcome.outcome with
    | .accepted value => some (outcome.targetField.field, value.render)
    | .noValue | .inheritedPoison _ => some (outcome.targetField.field, "-")
    | .invalidNoValue _ | .rejected _ _ => none)
  ["FS", "FB", "FD", "FE", "KS", "KB", "KD", "KE", "FN"].mapM fun name =>
    (found.find? (·.1 == idOf name)).map (·.2)

private def full : List String := ["x", "true", "2020-01-01", "A", "7", "1"]

/- `o1` against `o2` and `o4`: the only filled third row, beyond the capacity of two, is left out, so
every scan clears as with no filled row and every guard computes, and `FN` reads `0`. -/
example :
    values? [[], [], full] = some ["-", "-", "-", "-", "1", "1", "1", "1", "0"] ∧
      values? [[], full] = some ["x", "true", "2020-01-01", "A", "-", "-", "-", "-", "7"] ∧
      values? [[], []] = some ["-", "-", "-", "-", "1", "1", "1", "1", "0"] := by
  native_decide

/- `o3`: a malformed in-capacity `Day` poisons its scan, which clears `KD` where exhaustion computes it,
and a malformed kept `Num` clears `FN`. -/
example :
    values? [[], ["x", "true", "bad", "A", "x", "1"]] =
      some ["x", "true", "-", "A", "-", "-", "-", "-", "-"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanFirstFilledCapacity
