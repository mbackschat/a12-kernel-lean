import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.ScalarComputationRun

/-! # Authored repeatable Number plan locks: the row target's boundary

The [row-target boundary grid](../../docs/sources/computation-scheduling-probes.md#src-row-target-boundary):
a repeatable `Rg/Rows` (at most three rows) holding a nested repeatable `Sub`, beside a repeatable
sibling `Oth` and a fixed `Fx`. Its runtime document computes, at every row, `TLEN = Length(S1)`,
`TDAY = DayFromDate(D)`, `TTOK = NumberOfValueInFields("a" In S1, S2)` and
`TBOOL = NumberOfValueInFields(True In B1, B2)`, and at every inner row `IT = Max([../A], [IA])` and
`IG = 1` under a guard authored by name, `FieldFilled(../A)`. Every target holds a stale `99`, and the
outcomes are the Kernel's, measured on both codegen strategies.

Its static models fix the row target's refusals: a read below the target's levels and a read of the
sibling group draw `MVK_NO_WILDCARD`, a row target outside the declaring group the placement class
ahead of a String copy's comparison class, and a String copied inside the row the comparison class.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowBoundary

open A12Kernel

private def rows : GroupPath := ["Rg", "Rows"]
private def sub : GroupPath := ["Rg", "Rows", "Sub"]

private def number : FieldKind := .number { scale := 0, signed := true }

private def fieldSpecs : List (String × GroupPath × List RepeatableLevel × FieldKind) :=
  [("A", rows, [10], number), ("S1", rows, [10], .string), ("S2", rows, [10], .string),
    ("B1", rows, [10], .boolean), ("B2", rows, [10], .boolean),
    ("D", rows, [10], .temporal .date TemporalComponents.fullDate),
    ("TLEN", rows, [10], number), ("TDAY", rows, [10], number),
    ("TTOK", rows, [10], number), ("TBOOL", rows, [10], number),
    ("T", rows, [10], number),
    ("IA", sub, [10, 20], number), ("IT", sub, [10, 20], number),
    ("IG", sub, [10, 20], number),
    ("OX", ["Rg", "Oth"], [30], number), ("FX", ["Rg", "Fx"], [], number)]

private def idOf (name : String) : FieldId := (fieldSpecs.map (·.1)).idxOf name

private def model : FlatModel where
  fields := fieldSpecs.map fun (name, groupPath, repeatableScope, kind) =>
    { id := idOf name, groupPath, name, repeatableScope, policy := { kind } }
  repeatableGroups := [{ level := 10, path := rows, repeatability := some 3 },
    { level := 20, path := sub, repeatability := some 3 },
    { level := 30, path := ["Rg", "Oth"], repeatability := some 3 }]
  timeZoneId := "Europe/Berlin"

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }
private def parent (field : String) : SurfaceFieldPath := { base := .relative 1, groups := [], field }
private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def read (path : SurfaceFieldPath) : AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.field path))

private def pair (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

private def rowStep? (group : GroupPath) (target : String)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateCompleteNumericTargetComputationTable model group (idOf target) [(none, expression)]
    (targetScope := .row)).toOption

/-- `IG`'s guard is authored by name and resolved against the inner row, where `../A` is bound. -/
private def guarded? : Option (CheckedNumericComputationTable model) :=
  (elaborateNumericTargetComputationTableFromSurface model sub (idOf "IG")
    [(some (.fieldFilled (parent "A")), .literal { value := 1, authoredScale := 0 })]
    (targetScope := .row)).toOption

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  let steps ← [rowStep? rows "TLEN" (.atom (.numeric (.stringLength (bare "S1")))),
    rowStep? rows "TDAY" (.atom (.numeric (.temporalFieldPart (bare "D") (.date .day)))),
    rowStep? rows "TTOK" (.atom (.tokenValueCount "a"
      { first := .field (.direct (bare "S1")), rest := [.field (.direct (bare "S2"))] })),
    rowStep? rows "TBOOL" (.atom (.booleanValueCount true (pair "B1" "B2"))),
    rowStep? sub "IT" (.extremumCall .maximum (.extremum .maximum (read (parent "A")) (read (bare "IA")))),
    guarded?].mapM id
  (certifyRepeatableNumberPlan steps).toOption

private def cell (name : String) (path : List Nat) (text : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field := idOf name, path }, stored := text, raw
    numericDecimal := text.toInt?.map ({ unscaled := ·, scale := 0 }) }

private def num (name : String) (path : List Nat) (amount : Int) : ClassifiedCellInput :=
  cell name path (toString amount) (.parsed (.num amount))

private def text (name : String) (row : Nat) (value : String) : ClassifiedCellInput :=
  { address := { field := idOf name, path := [row] }, stored := value, raw := .parsed (.str value) }

private def flag (name : String) (row : Nat) (value : Bool) : ClassifiedCellInput :=
  { address := { field := idOf name, path := [row] }, stored := toString value
    raw := .parsed (.bool value) }

private def date (row : Nat) (stored : String) (year month day : Nat) : ClassifiedCellInput :=
  { address := { field := idOf "D", path := [row] }, stored
    raw := .parsed (.temporal (.date {
      instant := { epochMillis := 0 }
      parts := { year := (year : Int), month, day }
      basis := .storedGregorian })) }

private def seeds (row : Nat) (inner : List Nat) : List ClassifiedCellInput :=
  ["TLEN", "TDAY", "TTOK", "TBOOL"].map (num · [row] 99) ++
    inner.flatMap fun index => ["IT", "IG"].map (num · [row, index] 99)

/-- The grid's one document: three rows, the first with two inner rows and the second with one. -/
private def document? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] }, { group := 10, path := [2] }, { group := 20, path := [2, 1] },
      { group := 10, path := [3] }]
    cells := seeds 1 [1, 2] ++ seeds 2 [1] ++ seeds 3 [] ++
      [num "A" [1] 5, text "S1" 1 "abc", text "S2" 1 "a", flag "B1" 1 true, flag "B2" 1 false,
        date 1 "2024-06-15" 2024 6 15, num "IA" [1, 1] 3, num "IA" [1, 2] 9,
        text "S1" 2 "a", flag "B1" 2 true, flag "B2" 2 true, date 2 "2024-01-02" 2024 1 2,
        num "IA" [2, 1] 7,
        num "A" [3] 2, text "S1" 3 "a", text "S2" 3 "a",
        { address := { field := idOf "D", path := [3] }, stored := "x", raw := .rejected .dateFormat }]
  }).toOption

private def reported : NumericTargetOutcome → Option String
  | .accepted stored => some stored.render
  | .noValue | .inheritedPoison _ => some "-"
  | .rejected _ _ | .invalidNoValue _ => none

private def outcome? (name : String) (path : List Nat) : Option String := do
  let plan ← plan?
  let input ← document?
  let outcomes ← (plan.execute world input).toOption
  let found ← outcomes.find? (·.targetField == { field := idOf name, path })
  reported found.outcome

/- Every row of the grid: `Length`, `DayFromDate` and both value counts read their own row, a malformed
Date clearing only its row's `TDAY`; `Max` reads the enclosing row's `A` beside its own `IA`, an absent
`A` as `0`; and the guard authored by name reads the enclosing row's `A`, an absent one clearing `IG`. -/
example :
    [outcome? "TLEN" [1], outcome? "TDAY" [1], outcome? "TTOK" [1], outcome? "TBOOL" [1],
      outcome? "IT" [1, 1], outcome? "IG" [1, 1], outcome? "IT" [1, 2], outcome? "IG" [1, 2]] =
      [some "3", some "15", some "1", some "1", some "5", some "1", some "9", some "1"] ∧
    [outcome? "TLEN" [2], outcome? "TDAY" [2], outcome? "TTOK" [2], outcome? "TBOOL" [2],
      outcome? "IT" [2, 1], outcome? "IG" [2, 1]] =
      [some "1", some "2", some "1", some "2", some "7", some "-"] ∧
    [outcome? "TLEN" [3], outcome? "TDAY" [3], outcome? "TTOK" [3], outcome? "TBOOL" [3]] =
      [some "1", some "-", some "2", some "0"] := by
  native_decide

private def plain (path : SurfaceFieldPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field path)

/-- The class of `T`'s computation declared in `declaringGroup`, `none` when it is admitted. -/
private def classOf (declaringGroup : GroupPath) (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : Option SurfaceComputationCondition := none) : Option KernelStaticDiagnostic :=
  match elaborateNumericTargetComputationTableFromSurface model declaringGroup (idOf "T")
      [(guard, expression)] (targetScope := .row) with
  | .error error => error.diagnostic?
  | .ok _ => none

/- The static models, each the Kernel's sole code: a read below the target's levels, alone or inside
`Max`, and a read of the sibling repeatable group; a Number and a String copied into the row target
from the fixed `Fx`, which it does not lie below, and a guarded constant from there; and a String
copied inside the row. -/
example :
    classOf rows (plain (absolute ["Rg", "Rows", "Sub"] "IA")) = some .noWildcard ∧
    classOf rows (.extremumCall .maximum (.extremum .maximum
      (plain (absolute ["Rg", "Rows", "Sub"] "IA")) (plain (bare "A")))) = some .noWildcard ∧
    classOf rows (plain (absolute ["Rg", "Oth"] "OX")) = some .noWildcard ∧
    classOf ["Rg", "Fx"] (plain (absolute rows "A")) = some .fieldNotInRuleGroup ∧
    classOf ["Rg", "Fx"] (plain (absolute rows "S1")) = some .fieldNotInRuleGroup ∧
    classOf ["Rg", "Fx"] (.literal { value := 1, authoredScale := 0 })
      (some (.fieldFilled (absolute rows "A"))) = some .fieldNotInRuleGroup ∧
    classOf rows (plain (bare "S1")) = some .invalidCompareToEnumOrString ∧
    classOf rows (plain (bare "A")) = none := by
  native_decide

/- No fixed consumer accepts a row table: the scalar plan refuses it as needing a repeatable context,
and the default fixed scope refuses the same row target outright. A String expression judged in the
repeating row group is refused before its operands. -/
example :
    (match rowStep? rows "TLEN" (.atom (.numeric (.stringLength (bare "S1")))) with
      | some table => (certifyScalarComputationPlan [.number table] matches
          .error (.repeatableContextRequired _))
      | none => false) = true ∧
    (elaborateCompleteNumericTargetComputationTable model rows (idOf "TLEN")
      [(none, .atom (.numeric (.stringLength (bare "S1"))))]).toOption.isNone ∧
    (elaborateStringExpr model rows (.field (bare "S1")) matches
      .error (.repeatableTargetGroup _)) := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowBoundary
