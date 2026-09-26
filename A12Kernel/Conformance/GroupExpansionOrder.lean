import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TemporalExtremumOperands

/-! # A12Kernel.Conformance.GroupExpansionOrder — which expanded field a group operand leads with

A group operand is its fields, and the kind gates read them in one order: depth-first in declaration
order, a subgroup's fields standing at the subgroup's position and an index field at its own. The
peer's `EntityListGroupExpansionKindLawsTest` rows fix that order on the Kernel
([inbound](../../docs/SOURCES.md#inbound-2026-09-26i-expansion-order)); here the fixture lists its
fields depth-first, the representation contract `FlatModel.fields` states, and every row is one of
the peer's on groups of the same kinds and nesting, whose names and root-level order differ from
the peer's without any locked row depending on them. Each positional row separates an account: a later field
leading, an index field leading wherever declared, direct fields expanded ahead of a subgroup's, or a
subgroup's ahead of direct fields.
-/

namespace A12Kernel.Conformance.GroupExpansionOrder

open A12Kernel

private def number (id : Nat) (groupPath : GroupPath) (name : String)
    (repeatableScope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath, name, repeatableScope, policy := { kind := .number { scale := 0, signed := false } } }

private def text (id : Nat) (groupPath : GroupPath) (name : String)
    (repeatableScope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath, name, repeatableScope, policy := { kind := .string } }

private def date (id : Nat) (groupPath : GroupPath) (name format : String) (day : Bool)
    (repeatableScope : List RepeatableLevel := []) : FlatFieldDecl :=
  let components : TemporalComponents :=
    { year := true, month := true, day, hour := false, minute := false, second := false }
  { id, groupPath, name, repeatableScope,
    policy := { kind := .temporal .date components },
    temporalTargetPolicy := some { format } }

private def itemModel : FlatModel :=
  { fields := [
      text 1 ["Item"] "Title",
      number 2 ["Item"] "Weight",
      date 3 ["Item"] "Released" "dd.MM.yyyy" true,
      number 4 ["Item", "Grading"] "First",
      number 5 ["Item", "Grading"] "Second",
      text 6 ["Item", "Specs"] "Label",
      number 7 ["Item", "Specs"] "Depth",
      text 8 ["Item", "Nested", "Inner"] "Note",
      number 9 ["Item", "NumNested", "Inner"] "Count",
      text 10 ["Item", "Layered", "Sheet"] "Line",
      number 11 ["Item", "Layered"] "Count",
      number 12 ["Item", "Annotated"] "Pieces",
      text 13 ["Item", "Annotated", "Memo"] "Remark",
      text 14 ["Item", "Keyed"] "Key" [10],
      number 15 ["Item", "Keyed"] "Amount" [10],
      number 16 ["Item", "Rekeyed"] "Tally" [11],
      text 17 ["Item", "Rekeyed"] "Code" [11],
      date 18 ["Item", "Dated"] "Start" "dd.MM.yyyy" true [12],
      date 19 ["Item", "Dated"] "End" "dd.MM.yyyy" true [12],
      date 20 ["Item", "Monthly"] "Start" "yyyy-MM" false [13],
      date 21 ["Item", "Monthly"] "End" "yyyy-MM" false [13]]
    repeatableGroups := [
      { level := 10, path := ["Item", "Keyed"], indexField := some 14 },
      { level := 11, path := ["Item", "Rekeyed"], indexField := some 17 },
      { level := 12, path := ["Item", "Dated"] },
      { level := 13, path := ["Item", "Monthly"] }] }

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def group (name : String) : SurfaceFieldEntityOperand :=
  .group (.path { base := .relative 0, groups := [name] })

private def starred (name : String) : SurfaceFieldEntityOperand :=
  .starredGroup { base := .relative 0, groups := [{ name, starred := true }] }

private def listOf : List SurfaceFieldEntityOperand → SurfaceFieldEntitySource
  | [] => { first := field "Weight", rest := [] }
  | first :: rest => { first, rest }

/-- The Number carrier's verdict: `none` when admitted, otherwise the class `op` projects. -/
private def numberVerdict (op : NumericAggregateOp) (operands : List SurfaceFieldEntityOperand) :
    Option (Option KernelStaticDiagnostic) :=
  match elaborateNumberEntitySource itemModel ["Item"] (listOf operands) with
  | .ok _ => none
  | .error error => some (error.aggregateDiagnostic? op)

private def tokenDistinctVerdict (operands : List SurfaceFieldEntityOperand) :
    Option (Option KernelStaticDiagnostic) :=
  match elaborateTokenDistinctCountSource itemModel ["Item"] (listOf operands) with
  | .ok _ => none
  | .error error => some error.diagnostic?

private def temporalVerdict (operands : List SurfaceFieldEntityOperand) :
    Option (Option KernelStaticDiagnostic) :=
  match TemporalExtremumOperands.elaborate itemModel ["Item"] (listOf operands) with
  | .ok _ => none
  | .error error => some error.diagnostic?

example : itemModel.validate.isOk = true := by native_decide

/- The first expanded field sets the family. `Specs` leads with its String and `Annotated` with its
   Number, `Layered` with the String of its earlier subgroup, and `Rekeyed` with its Number although
   its index field is a String declared after it. The String family's class is the token distinct
   count's and the Number family's the Number carrier's, each leaving the other's list unclassed. -/
example :
    tokenDistinctVerdict [group "Specs", field "Weight"] = some (some .stringEnumAndNonStringEnum) ∧
    numberVerdict .distinctCount [group "Specs", field "Weight"] = some none ∧
    tokenDistinctVerdict [group "Layered", field "Weight"] =
      some (some .stringEnumAndNonStringEnum) ∧
    numberVerdict .distinctCount [group "Annotated", field "Weight"] =
      some (some .numberAndNonNumber) ∧
    numberVerdict .distinctCount [starred "Rekeyed", field "Title"] =
      some (some .numberAndNonNumber) ∧
    numberVerdict .distinctCount [group "Grading", field "Weight"] = none := by
  native_decide

/- The expansion holds the index field and reaches any depth: `Keyed` holds a String key, so `Sum`
   refuses it and the distinct count leads with it, and `Nested` holds a String two levels down. A
   lone group is judged as its fields, and the Number-only controls are admitted. -/
example :
    numberVerdict .sum [starred "Keyed"] = some (some .noNumber) ∧
    tokenDistinctVerdict [starred "Keyed", field "Title"] =
      some (some .stringEnumAndNonStringEnum) ∧
    numberVerdict .sum [group "Nested"] = some (some .noNumber) ∧
    numberVerdict .sum [group "Specs"] = some (some .noNumber) ∧
    numberVerdict .sum [group "NumNested", field "Weight"] = none ∧
    numberVerdict .sum [group "Grading"] = none := by
  native_decide

/- The extrema's date walk reads a group's fields behind a temporal leader: a non-date field draws
   the family class and a year-month pair the component-set class, against a same-format control. -/
example :
    temporalVerdict [field "Released", starred "Keyed"] = some (some .dateAndNonDate) ∧
    temporalVerdict [field "Released", starred "Monthly"] =
      some (some .dateFormatsNotCompatible) ∧
    temporalVerdict [starred "Dated", field "Released"] = none := by
  native_decide

end A12Kernel.Conformance.GroupExpansionOrder
