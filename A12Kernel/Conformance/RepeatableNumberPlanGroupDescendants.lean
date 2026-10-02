import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored Number plan locks: a fixed group read through its repeatable descendant

A root `Rg` holds fixed `GB`, `GT` and `GN` over repeatable `RB` of Boolean `B`, `RT` of String `T` and
`RN` of Number `N1` and `N2`, each at most two rows. Fixed root targets read them as groups:
`BV = NumberOfValueInFields(True In GB)`, `TV = NumberOfValueInFields("a" In GT)`,
`NV = NumberOfValueInFields(1 In GN)`, `FF = FirstFilledValue(GN)` and `SN = Sum(GN)`, every target
seeded with `99`. The documents are the Kernel's rows of the
[descendant grid](../../evidence/kernel-30.8.1/captures/fixed-group-descendants-2026-10-02/), measured
on both codegen strategies.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanGroupDescendants

open A12Kernel

private def targets : List String := ["BV", "TV", "NV", "FF", "SN"]

private def names : List String := targets ++ ["B", "T", "N1", "N2"]

private def idOf (name : String) : FieldId := names.idxOf name

private def declaration (name : String) : FlatFieldDecl :=
  let (groupPath, repeatableScope, kind) : GroupPath × List RepeatableLevel × FieldKind :=
    match name with
    | "B" => (["Rg", "GB", "RB"], [10], .boolean)
    | "T" => (["Rg", "GT", "RT"], [20], .string)
    | "N1" | "N2" => (["Rg", "GN", "RN"], [30], .number { scale := 0, signed := true })
    | _ => (["Rg"], [], .number { scale := 0, signed := true })
  { id := idOf name, groupPath, name, repeatableScope, policy := { kind } }

private def model : FlatModel where
  fields := names.map declaration
  repeatableGroups := [{ level := 10, path := ["Rg", "GB", "RB"], repeatability := some 2 },
    { level := 20, path := ["Rg", "GT", "RT"], repeatability := some 2 },
    { level := 30, path := ["Rg", "GN", "RN"], repeatability := some 2 }]

private def group (name : String) : SurfaceFieldEntityOperand :=
  .group (.path { base := .relative 0, groups := [name] })

private def expression : String → AuthoredNumericExpr SurfaceNumericComputationAtom
  | "BV" => .atom (.booleanValueCount true { first := group "GB", rest := [] })
  | "TV" => .atom (.tokenEntityValueCount "a" { first := group "GT", rest := [] })
  | "NV" => .atom (.valueCount 1 { first := group "GN", rest := [] })
  | "FF" => .atom (.firstFilled { first := group "GN", rest := [] })
  | _ => .atom (.numeric (.aggregate .sum { first := group "GN", rest := [] }))

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  let steps ← targets.mapM fun target =>
    (elaborateCompleteNumericTargetComputationTable model ["Rg"] (idOf target)
      [(none, expression target)]).toOption
  (certifyRepeatableNumberPlan steps).toOption

/-- A cell parsed by its field's kind, a Number text that is no integer rejected as malformed. -/
private def cell (name : String) (path : List Nat) (text : String) : ClassifiedCellInput :=
  let raw : RawCell := match (declaration name).policy.kind with
    | .boolean => classifyStoredBooleanText text
    | .string => .parsed (.str text)
    | _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
  { address := { field := idOf name, path }, stored := text, raw
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

/-- One document of the given `RB`, `RT` and `RN` rows, each row's texts with `""` for an absent cell. -/
private def document? (rb rt : List String) (rn : List (String × String)) :
    Option (CheckedDocument model) :=
  let rows (level : RepeatableLevel) (count : Nat) : List RowAddr :=
    (List.range count).map fun index => { group := level, path := [index + 1] }
  let present (name : String) (index : Nat) (text : String) : List ClassifiedCellInput :=
    if text == "" then [] else [cell name [index + 1] text]
  (checkDocument prepared "en_US" {
    instantiatedRows := rows 10 rb.length ++ rows 20 rt.length ++ rows 30 rn.length
    cells := targets.map (cell · [] "99") ++
      (rb.zipIdx.flatMap fun (text, index) => present "B" index text) ++
      (rt.zipIdx.flatMap fun (text, index) => present "T" index text) ++
      rn.zipIdx.flatMap fun ((n1, n2), index) => present "N1" index n1 ++ present "N2" index n2
  }).toOption

/-- The stored amount; a cleared target as `-` when it is clean and `poison` when it carries a read
fault, both of which the Kernel reports as cleared. -/
private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue => some "-"
  | .inheritedPoison _ => some "poison"
  | .invalidNoValue _ | .rejected _ _ => none

/-- Every outcome as `target value`, sorted. -/
private def outcomes? (rb rt : List String) (rn : List (String × String)) :
    Option (List String) := do
  let outcomes ← ((← plan?).execute world (← document? rb rt rn)).toOption
  let rendered ← outcomes.mapM fun outcome => (reported outcome.outcome).map fun value =>
    s!"{names.getD outcome.targetField.field ""} {value}"
  pure (rendered.mergeSort (decide <| · ≤ ·))

/- `f01`: every row of each descendant is read, and `FirstFilledValue` takes the first declaration's
rows before the second's, so `N1` at the second row comes ahead of `N2` at the first; reading row by row
answers `2`. -/
example :
    outcomes? ["false", "true"] ["a", "a"] [("", "2"), ("1", "")] =
      some ["BV 1", "FF 1", "NV 1", "SN 3", "TV 2"] := by
  native_decide

/- `f02`: a match in an over-limit third row is left out of every count, scan and aggregate. -/
example :
    outcomes? ["", "", "true"] ["", "", "a"] [("", ""), ("", ""), ("1", "")] =
      some ["BV 0", "FF 0", "NV 0", "SN 0", "TV 0"] := by
  native_decide

/- `f03`: a malformed `B` or `N1` member poisons the counts, scan and sum reading it, while the String
count computes. -/
example :
    outcomes? ["true", "maybe"] ["a", "b"] [("", "2"), ("x", "")] =
      some ["BV poison", "FF poison", "NV poison", "SN poison", "TV 1"] := by
  native_decide

/- `f04` and `f05`: groups without rows answer `0`, and a match in the second row alone is found. -/
example :
    outcomes? [] [] [] = some ["BV 0", "FF 0", "NV 0", "SN 0", "TV 0"] ∧
      outcomes? ["", "true"] ["", "a"] [("", ""), ("", "2")] =
        some ["BV 1", "FF 2", "NV 0", "SN 2", "TV 1"] := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanGroupDescendants
