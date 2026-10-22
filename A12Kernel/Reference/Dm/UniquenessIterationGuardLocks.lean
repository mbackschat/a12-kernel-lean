import A12Kernel.Reference.Dm.Validate

/-! # The uniqueness iteration guard across carriers and operand shapes

Each expected class is the Kernel's model-check verdict for the same condition reported on the
iterated row's field, in the retained
[uniqueness-iteration-guard capture](../../../docs/sources/having-filter-probes.md#src-uniqueness-iteration-guard).
The rows separate the slot count of a root field, a wildcard, a semantic-index selection and a group
operand, so a guard counting an operand rather than the fields it reads fails a row. -/

namespace A12Kernel.Dm.UniquenessIterationGuardLocks

open A12Kernel

private def policy (kind : Char) : FlatFieldDecl → FlatFieldDecl := fun field =>
  match kind with
  | 'N' => { field with policy := { kind := .number { scale := 0, signed := true } } }
  | 'D' => { field with policy := { kind := .temporal .date .fullDate }
                        temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  | _ => { field with policy := { kind := .string } }

private def kinds : List Char := ['N', 'T', 'D']

/-- Each kind's fields under `group`, named by `names`, numbered from `base`. -/
private def fields (base : Nat) (group : GroupPath) (scope : List RepeatableLevel)
    (names : Char → List String) : List FlatFieldDecl :=
  (kinds.zipIdx.flatMap fun (kind, i) => (names kind).zipIdx.map fun (name, j) =>
    policy kind { id := base + 10 * i + j, name, groupPath := group, repeatableScope := scope, policy := { kind := .string } })

private def pair (kind : Char) (stem : String) : List String :=
  [stem ++ kind.toString ++ "1", stem ++ kind.toString ++ "2"]

private def model : FlatModel :=
  { fields :=
      fields 100 ["Form"] [] (fun k => pair k "O") ++
      fields 200 ["Form", "Rows"] [10] (fun k => [k.toString]) ++
      kinds.zipIdx.flatMap (fun (k, i) => fields (300 + 30 * i) ["Form", "Rows", "Pair" ++ k.toString] [10]
        (fun k' => if k' == k then pair k "P" else [])) ++
      fields 400 ["Form", "W"] [20] (fun k => [k.toString]) ++
      [policy 'T' { id := 500, name := "Key", groupPath := ["Form", "K"], repeatableScope := [30], policy := { kind := .string } }] ++
      fields 510 ["Form", "K"] [30] (fun k => [k.toString]) ++
      kinds.zipIdx.flatMap (fun (k, i) => fields (600 + 30 * i) ["Form", "K", "KG" ++ k.toString] [30]
        (fun k' => if k' == k then pair k "KG" else [])) ++
      kinds.zipIdx.flatMap (fun (k, i) => fields (700 + 30 * i) ["Form", "G" ++ k.toString] []
        (fun k' => if k' == k then pair k "G" else [])) ++
      kinds.zipIdx.flatMap (fun (k, i) => fields (800 + 30 * i) ["Form", "H" ++ k.toString] []
        (fun k' => if k' == k then ["H" ++ k.toString ++ "1"] else []))
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 3 },
      { level := 20, path := ["Form", "W"], repeatability := some 2 },
      { level := 30, path := ["Form", "K"], repeatability := some 3, indexField := some 500 }] }

private def verdictIn (flat : FlatModel) (target condition : String) : String :=
  let dm : DmModel := { flat, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkRule dm .english {
      group := ["Form"], name := "Guard", errorCode := "GUARD", errorEntityRelPath := target,
      condition, severity := "ERROR" } with
  | .ok _ => "admitted"
  | .error refusal =>
      if refusal.detail.startsWith "MVK_NEG_CONDITION_IN_ITERATION A12Kernel.FlatRuleAssemblyError.negativeConditionInIteration"
      then "MVK_NEG_CONDITION_IN_ITERATION" else refusal.detail

private def verdict := verdictIn model

private def admitted := "admitted"
private def refused := "MVK_NEG_CONDITION_IN_ITERATION"

/-- `(name, operands after the row field, expected)`; `{x}` is the carrier letter. -/
private def rows : List (String × String × String) := [
  ("ROOT1", "O{x}1", admitted), ("ROOT2", "O{x}1, O{x}2", refused), ("STAR2", "W*/{x}", refused),
  ("SEL1", "K/{x} For \"k1\"", admitted), ("SEL2", "K/{x} For \"k1\", K/{x} For \"k2\"", refused),
  ("SELROOT", "K/{x} For \"k1\", O{x}1", refused), ("ROWGRP", "Rows/Pair{x}", admitted),
  ("ROOTGRP", "G{x}", refused), ("SELGRP", "K/KG{x} For \"k1\"", refused),
  ("ROOTGRP1", "H{x}", admitted), ("ROOTGRP1F", "H{x}, O{x}1", refused)]

example : model.validate.isOk = true := by native_decide

private def number (id : FieldId) (name : String) (group : GroupPath) (scope : List RepeatableLevel) :
    FlatFieldDecl := policy 'N' { id, name, groupPath := group, repeatableScope := scope, policy := { kind := .string } }

/-- A repeatable level inside a group or below a selection weighs its fields by its capacity, and a
group inside the iterated row still supplies none. -/
private def nestedModel : FlatModel :=
  { model with
    fields := model.fields ++ [
      number 900 "R1" ["Form", "Rows", "RG"] [10], number 901 "R2" ["Form", "Rows", "RG", "RD"] [10, 40],
      number 902 "D1" ["Form", "GR1", "Deep"] [50], number 903 "E1" ["Form", "GR2"] [],
      number 904 "D2" ["Form", "GR2", "Deep"] [60], number 905 "K1" ["Form", "K", "KD", "KR"] [30, 70]]
    repeatableGroups := model.repeatableGroups ++ [
      { level := 40, path := ["Form", "Rows", "RG", "RD"], repeatability := some 2 },
      { level := 50, path := ["Form", "GR1", "Deep"], repeatability := some 2 },
      { level := 60, path := ["Form", "GR2", "Deep"], repeatability := some 2 },
      { level := 70, path := ["Form", "K", "KD", "KR"], repeatability := some 2 }] }

example : nestedModel.validate.isOk = true := by native_decide

example :
    let verdict := fun condition => verdictIn nestedModel "../Rows/N" condition
    verdict "FieldValuesNotUnique(Rows/N, GR1)" = refused ∧
    verdict "FieldValuesNotUnique(Rows/N, GR2)" = refused ∧
    verdict "FieldValuesNotUnique(Rows/N, GR1/Deep*)" = refused ∧
    verdict "FieldValuesNotUnique(Rows/N, K/KD For \"k1\")" = refused ∧
    verdict "FieldValuesNotUnique(Rows/N, Rows/RG)" = admitted := by native_decide

example : kinds.all (fun kind =>
    let x := kind.toString
    rows.all (fun (_, operands, expected) =>
      verdict ("../Rows/" ++ x) ("FieldValuesNotUnique(Rows/" ++ x ++ ", " ++ operands.replace "{x}" x ++ ")") ==
        expected) &&
    verdict ("../Rows/Pair" ++ x ++ "/P" ++ x ++ "1") ("FieldValuesNotUnique(Rows/Pair" ++ x ++ ")") == admitted &&
    verdict ("../Rows/Pair" ++ x ++ "/P" ++ x ++ "1") ("FieldValuesNotUnique(Rows/Pair" ++ x ++ ", O" ++ x ++ "1)") ==
      admitted) = true := by native_decide

end A12Kernel.Dm.UniquenessIterationGuardLocks
