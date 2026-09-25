import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Elaboration.ValidationRuleGroupOperand
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.NumericAggregate.Fields
import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Elaboration.EnumerationFirstFilledComputation

/-! # What binds a read's repeatable levels

A validation read's levels are bound by the error field's repeatable scope when the error field lies
at or below the rule group, and by nothing when it lies outside: then every level draws the
containment class, the rule group's own included. A level holding the error field is bound, so the
Kernel admits the read; the evaluators here read at the rule group's own scope, so they refuse it
claiming no class. Every other unbound level takes the walk's class, which reaches the aggregate
operand list and a filter's marked reference too, and a computation's target places the class on
every carrier. The semantic-index group count keeps its own refusal at every locus. Each expected
value is a verdict from the walk batch grid, its rule or observation id named beside it
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)),
or a row of the peer's index-type table, which the case's comment cites; the walk past a legal pair
of two kinds is this project's assumption, and its case says so.
-/

namespace A12Kernel.Conformance.ReadingScope

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := false } }
private def text : FieldPolicy := { kind := .string }

/-- The grid's policy sheet: a keyed `Claims` and an unkeyed `Plain`, each holding a fixed `Sub`
    and `Seal2`, beside a fixed `Insured`. -/
private def policyModel : FlatModel :=
  let field (id : FieldId) (groups : List String) (name : String) (policy : FieldPolicy)
      (scope : List RepeatableLevel) : FlatFieldDecl :=
    { id, groupPath := "Policy" :: groups, name, policy, repeatableScope := scope }
  let range (id : FieldId) (groups : List String) (name : String)
      (scope : List RepeatableLevel) : FlatFieldDecl :=
    { field id groups name { kind := .dateRange } scope with
      dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }
  { fields := [
      field 1 [] "Holder" text [], field 2 [] "Base" number [],
      field 3 ["Insured"] "Remark" text [],
      field 4 ["Claims"] "ClaimRef" text [10], field 5 ["Claims"] "Amount" number [10],
      range 6 ["Claims"] "R1" [10], range 7 ["Claims"] "R2" [10],
      field 8 ["Claims", "Sub"] "SubAmount" number [10],
      field 9 ["Claims", "Seal2"] "S2Note" text [10],
      field 10 ["Plain"] "PAmount" number [20], range 11 ["Plain"] "PR1" [20],
      range 12 ["Plain"] "PR2" [20], field 13 ["Plain", "PSub"] "PSubAmount" number [20],
      field 14 ["Plain", "PSeal2"] "PS2Note" text [20]]
    repeatableGroups := [
      { level := 10, path := ["Policy", "Claims"], repeatability := some 2, indexField := some 4 },
      { level := 20, path := ["Policy", "Plain"], repeatability := some 2 }] }

private def g (groups : List String) : GroupPath := "Policy" :: groups
private def p (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := "Policy" :: groups, field }
private def rel (up : Nat) (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .relative up, groups, field }

private abbrev Verdict := Option (Option KernelStaticDiagnostic)

/-- A carrier's verdict: `none` when it is admitted, otherwise the class its refusal projects. -/
private def verdict (result : Except ε α) (class? : ε → Option KernelStaticDiagnostic) : Verdict :=
  match result with
  | .ok _ => none
  | .error error => some (class? error)

private def noIndex : Verdict := some (some .errorFieldNoIndex)
private def noWildcard : Verdict := some (some .noWildcard)
private def containment : Verdict := some (some .fieldNotInRuleGroup)
/-- A refusal claiming no class: here, a read the Kernel admits at a scope this carrier does not
    evaluate. -/
private def unclassed : Verdict := some none

private def numericClass : NumericValidationElabError → Option KernelStaticDiagnostic
  | .resolve error => error.diagnostic?
  | .aggregate (.resolve error) => error.diagnostic?
  | _ => none

private def gtZero (left : SurfaceNumericAtom) : SurfaceNumericComparison :=
  { op := .ordinary .greater, left := .atom left, right := .literal { value := 0, authoredScale := 0 } }

/-- `[path] > 0` in a rule at `rowGroup` whose error field lies in `writtenGroup`. -/
private def read (rowGroup writtenGroup : GroupPath) (path : SurfaceFieldPath) : Verdict :=
  verdict (elaborateNumericComparison policyModel rowGroup (gtZero (.field path)) writtenGroup)
    numericClass

/-- `op(first, second) > 0` over the comparison's own aggregate operand list. -/
private def aggregate (rowGroup writtenGroup : GroupPath) (op : NumericAggregateOp)
    (first second : SurfaceFieldPath) : Verdict :=
  verdict (elaborateNumericComparison policyModel rowGroup
      (gtZero (.aggregate op { first, rest := [second] })) writtenGroup) numericClass

private def fieldFilled (rowGroup writtenGroup : GroupPath) (path : SurfaceFieldPath) : Verdict :=
  verdict (elaborate policyModel rowGroup (.fieldFilled path) writtenGroup)
    fun | .resolve error => error.diagnostic? | _ => none

private def entity (rowGroup writtenGroup : GroupPath) (source : SurfaceNumberEntitySource) :
    Verdict :=
  verdict (elaborateNumberEntitySource policyModel rowGroup source (writtenGroup := writtenGroup))
    (NumberEntityElabError.aggregateDiagnostic? .sum)

private def starOf (group field : String) : SurfaceStarFieldPath :=
  { base := .absolute, groups := [{ name := "Policy" }, { name := group, starred := true }], field }

/-! ## The aggregate operand list -/

/- `Sum` and `MaxValue` over a plain list follow the walk like a bare read (`Rf4ctlk`, `Rf4ctlp`):
   the index class beside the keyed `Claims` (`Rf4sumk`, `Rf4maxk`), the missing star beside `Plain`
   (`Rf4sump`), containment with the error field outside the rule group (`Rf4outk`, `Rf4outp`), and
   the missing star below the error field's group (`Rf4rootk`). -/
example :
    [aggregate (g []) (g ["Insured"]) .sum (p [] "Base") (p ["Claims"] "Amount"),
      aggregate (g []) (g ["Insured"]) .sum (p [] "Base") (p ["Plain"] "PAmount"),
      aggregate (g []) (g ["Insured"]) .maximum (p [] "Base") (p ["Claims"] "Amount"),
      read (g []) (g ["Insured"]) (p ["Claims"] "Amount"),
      read (g []) (g ["Insured"]) (p ["Plain"] "PAmount"),
      aggregate (g ["Insured"]) (g []) .sum (p [] "Base") (p ["Claims"] "Amount"),
      aggregate (g ["Insured"]) (g []) .sum (p [] "Base") (p ["Plain"] "PAmount"),
      aggregate (g []) (g []) .sum (p [] "Base") (p ["Claims"] "Amount")] =
    [noIndex, noWildcard, noIndex, noIndex, noWildcard, containment, containment, noWildcard] := by
  native_decide

/-! ## A level holding the error field -/

/- From a rule at the root, an error field in `Claims/Sub` binds `Claims`: the Kernel admits the
   error field's own presence (`Rf16kalone`, `Rf16palone`), a read of the level with the error field
   below it or in it (`Rf16k`, `Rf16p`, `Rf16kown`), and a `Sum` over it (`Rf16ksum`), each of which
   these carriers refuse claiming no class. The sibling `Plain` stays unbound (`Rf16ksib`), a star
   needs no binding (`Rf16kstar`), and from `Insured` the error field lies outside (`Rf16kins`). -/
example :
    [fieldFilled (g []) (g ["Claims", "Sub"]) (p ["Claims", "Sub"] "SubAmount"),
      fieldFilled (g []) (g ["Plain", "PSub"]) (p ["Plain", "PSub"] "PSubAmount"),
      read (g []) (g ["Claims", "Sub"]) (p ["Claims"] "Amount"),
      read (g []) (g ["Plain", "PSub"]) (p ["Plain"] "PAmount"),
      read (g []) (g ["Claims"]) (p ["Claims"] "Amount"),
      aggregate (g []) (g ["Claims", "Sub"]) .sum (p ["Claims"] "Amount") (p [] "Base"),
      read (g []) (g ["Claims", "Sub"]) (p ["Plain"] "PAmount"),
      entity (g []) (g ["Claims", "Sub"]) { first := .star (starOf "Claims" "Amount"), rest := [] },
      read (g ["Insured"]) (g ["Claims", "Sub"]) (p ["Claims"] "Amount")] =
    List.replicate 6 unclassed ++ [noWildcard, none, containment] := by
  native_decide

/- The rule-owned group projections admit `GroupFilled(Claims)` (`Rf16kgf`) and
   `AllGroupsFilled(Claims, Insured)` (`Rf16kagf`) with that error field. -/
example :
    projectGroupFilledRuleAdmission policyModel (g []) 8
        (.path { base := .absolute, groups := ["Policy", "Claims"] }) = .admitted ∧
      projectGroupListRuleAdmission policyModel (g []) 8 .allGroupsFilled
        [.group (.path { base := .absolute, groups := ["Policy", "Claims"] }),
          .group (.path { base := .absolute, groups := ["Policy", "Insured"] })] = .admitted := by
  native_decide

/-! ## Nothing binds a level from outside -/

private def groupAndBase (group : String) : SurfaceNumberEntitySource :=
  let sub : SurfaceGroupReference := .path { base := .relative 0, groups := [group] }
  { first := .group sub, rest := [.field (p [] "Base")] }

private def presence (rowGroup : GroupPath) (path : SurfaceFieldPath) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence policyModel rowGroup .filled path).toOption

private def assembled (condition : CheckedValidationCondition policyModel) (errorField : FieldId) :
    Verdict :=
  verdict (assembleResolvedValidationRule policyModel condition errorField "R" .error { parts := [] })
    FlatRuleAssemblyError.diagnostic?

/-- `FieldFilled(guard) And FieldFilled(other)` read by the repeatable presence carrier and
    assembled with `errorField`. -/
private def presenceRule (rowGroup : GroupPath) (guard other : SurfaceFieldPath)
    (errorField : FieldId) : Verdict :=
  match presence rowGroup guard, presence rowGroup other with
  | some left, some right =>
      match left.and right with
      | .ok whole => assembled whole errorField
      | .error _ => unclassed
  | _, _ => unclassed

/- The repeatable presence carrier derives the rule's iteration from the read, so it admits the error
   field's own presence as a whole rule, which the Kernel admits too (`Rf16kalone`, `Rf16palone`). -/
example :
    [(presence (g []) (p ["Claims", "Sub"] "SubAmount")).map (assembled · 8),
      (presence (g []) (p ["Plain", "PSub"] "PSubAmount")).map (assembled · 13)] =
    [some none, some none] := by
  native_decide

/- A rule in a repeatable group reporting on the root draws containment for its own row's field and
   for a fixed child of it, in the field slot and the group slot alike (`Rf17kfield`, `Rf17kgroup`,
   `Rf17pfield`, `Rf17pgroup`). -/
example :
    [aggregate (g ["Claims"]) (g []) .sum (rel 0 [] "Amount") (p [] "Base"),
      entity (g ["Claims"]) (g []) (groupAndBase "Sub"),
      aggregate (g ["Plain"]) (g []) .sum (rel 0 [] "PAmount") (p [] "Base"),
      entity (g ["Plain"]) (g []) (groupAndBase "PSub")] = List.replicate 4 containment := by
  native_decide

/- A rule in the fixed `Seal2` reporting on its parent row's field reads a level the rule group
   binds and still draws containment, at the read and as a whole rule, whose error scope matches its
   iteration (`Rl33k`, `Rl33p`). With the error field in `Seal2` the whole rule is admitted
   (`Rl33kin`); the lone read refuses it claiming no class, since the flat carrier reads no
   repeatable field. -/
example :
    [fieldFilled (g ["Claims", "Seal2"]) (g ["Claims"]) (rel 1 [] "Amount"),
      fieldFilled (g ["Plain", "PSeal2"]) (g ["Plain"]) (rel 1 [] "PAmount"),
      fieldFilled (g ["Claims", "Seal2"]) (g ["Claims", "Seal2"]) (rel 1 [] "ClaimRef"),
      presenceRule (g ["Claims", "Seal2"]) (rel 1 [] "Amount") (rel 1 [] "ClaimRef") 5,
      presenceRule (g ["Plain", "PSeal2"]) (rel 1 [] "PAmount") (rel 1 [] "PR1") 10,
      presenceRule (g ["Claims", "Seal2"]) (rel 0 [] "S2Note") (rel 1 [] "ClaimRef") 9] =
    [containment, containment, unclassed, containment, containment, none] := by
  native_decide

/-! ## The DateRange reader and a filter's marked reference -/

private def overlap (rowGroup writtenGroup : GroupPath) (first second : SurfaceFieldPath) : Verdict :=
  verdict (CheckedValidationCondition.fromIteratedDateRangeOverlap policyModel rowGroup
      { first := .field first, rest := [.field second] } writtenGroup)
    ValidationConditionAssemblyError.groupListDiagnostic?

/-- `Sum(<star> Having ([$<outer>] == [<inner>]))`. -/
private def filtered (star : SurfaceStarFieldPath) (outer inner : SurfaceFieldPath) :
    SurfaceNumberEntitySource :=
  { first := .starHaving star (.compareNumbers .equal { origin := .outer, field := outer }
      { origin := .inner, field := inner }), rest := [] }

/- `DateRangesOverlap` over a repeatable level's pair (`Rl20dk`, `Rl20dp`, `Rl20droot`) and a
   filter's marked reference into it (`Rl20fk`, `Rl20fp`) follow the walk from `Insured`: the index
   class for the keyed `Claims` and the missing star for `Plain`, and the missing star from the root. -/
example :
    [overlap (g ["Insured"]) (g ["Insured"]) (p ["Claims"] "R1") (p ["Claims"] "R2"),
      overlap (g ["Insured"]) (g ["Insured"]) (p ["Plain"] "PR1") (p ["Plain"] "PR2"),
      overlap (g []) (g []) (p ["Claims"] "R1") (p ["Claims"] "R2"),
      entity (g ["Insured"]) (g ["Insured"])
        (filtered (starOf "Plain" "PAmount") (p ["Claims"] "Amount") (p ["Plain"] "PAmount")),
      entity (g ["Insured"]) (g ["Insured"])
        (filtered (starOf "Claims" "Amount") (p ["Plain"] "PAmount") (p ["Claims"] "Amount"))] =
    [noIndex, noWildcard, noWildcard, noIndex, noWildcard] := by
  native_decide

/-! ## The semantic-index group count -/

/- `NumberOfFilledGroups(/Policy/Claims For "x") > 0` keeps its own class whatever the error field:
   the root (`Rf15in`), outside the rule group (`Rf15out`), beside `Claims` (`Rf15beside`), and inside
   it below a fixed child (`Rf15inside`). -/
example :
    let use : SurfaceFilledGroupCountSemanticIndexUse :=
      { group := { base := .absolute, groups := ["Policy", "Claims"] }, token := "x" }
    [projectFilledGroupCountSemanticIndexRuleAdmission policyModel (g []) 1 use,
      projectFilledGroupCountSemanticIndexRuleAdmission policyModel (g ["Insured"]) 1 use,
      projectFilledGroupCountSemanticIndexRuleAdmission policyModel (g []) 3 use,
      projectFilledGroupCountSemanticIndexRuleAdmission policyModel (g []) 8 use] =
    List.replicate 4 (.rejected .semanticIndexNotAllowed) := by
  native_decide

/-! ## Walk order and the index type gate -/

/-- The grid's route sheet: a keyed `Invoices` under a String `ShipmentKey`; an unkeyed `Ret`
    holding a keyed `Sub`; a keyed `Ref` under another name holding a keyed `Sub2`; and five groups
    keyed by a `ShipmentKey` of five kinds. The peer's type-table fixture adds five more kinds and a
    second Number scale, two of them holding an unkeyed group so a legal pair's walk shows. -/
private def routeModel : FlatModel :=
  let row (id : FieldId) (groups : List String) (name : String) (policy : FieldPolicy)
      (scope : List RepeatableLevel) : FlatFieldDecl :=
    { id, groupPath := "Fulfilment" :: groups, name, policy, repeatableScope := scope }
  let keyed (level : RepeatableLevel) (groups : List String) (key : FieldId) : RepeatableGroupDecl :=
    { level, path := "Fulfilment" :: groups, repeatability := some 2, indexField := some key }
  { fields := [
      row 1 [] "OrderTotal" number [],
      row 2 ["Invoices"] "ShipmentKey" text [1], row 3 ["Invoices"] "InvoiceNote" text [1],
      row 4 ["Ret"] "RetNote" text [2], row 5 ["Ret", "Sub"] "SubKey" text [2, 3],
      row 6 ["Ret", "Sub"] "SubAmount" number [2, 3],
      row 7 ["Ref"] "RefKey" text [4], row 8 ["Ref", "Sub2"] "Sub2Key" text [4, 5],
      row 9 ["Ref", "Sub2"] "Sub2Amount" number [4, 5],
      row 10 ["TagsS"] "ShipmentKey" text [6], row 11 ["TagsS"] "TAmount" number [6],
      row 12 ["TagsN"] "ShipmentKey" number [7], row 13 ["TagsN"] "TAmount" number [7],
      { row 14 ["TagsE"] "ShipmentKey" { kind := .enumeration } [8] with
        enumeration := some { storedTokens := ["A", "B"] } },
      row 15 ["TagsE"] "TAmount" number [8],
      row 16 ["TagsB"] "ShipmentKey" { kind := .boolean } [9], row 17 ["TagsB"] "TAmount" number [9],
      { row 18 ["TagsD"] "ShipmentKey" { kind := .temporal .date TemporalComponents.fullDate } [10]
        with temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      row 19 ["TagsD"] "TAmount" number [10],
      row 20 ["TagsC"] "ShipmentKey" { kind := .confirm } [11], row 21 ["TagsC"] "TAmount" number [11],
      { row 22 ["TagsM"] "ShipmentKey" { kind := .temporal .dateTime TemporalComponents.now } [12]
        with temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      row 23 ["TagsM"] "TAmount" number [12], row 24 ["TagsM", "Parts"] "PAmount" number [12, 13],
      { row 25 ["TagsT"] "ShipmentKey" { kind := .temporal .time TemporalComponents.time } [14]
        with temporalTargetPolicy := some { format := "HH:mm:ss" } },
      row 26 ["TagsT"] "TAmount" number [14],
      { row 27 ["TagsR"] "ShipmentKey" { kind := .dateRange } [15]
        with dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } },
      row 28 ["TagsR"] "TAmount" number [15],
      row 29 ["TagsN2"] "ShipmentKey" { kind := .number { scale := 2, signed := false } } [16],
      row 30 ["TagsN2"] "TAmount" number [16], row 31 ["TagsN2", "Parts2"] "PAmount" number [16, 17]]
    repeatableGroups := [
      keyed 1 ["Invoices"] 2, { level := 2, path := ["Fulfilment", "Ret"], repeatability := some 2 },
      keyed 3 ["Ret", "Sub"] 5, keyed 4 ["Ref"] 7, keyed 5 ["Ref", "Sub2"] 8,
      keyed 6 ["TagsS"] 10, keyed 7 ["TagsN"] 12, keyed 8 ["TagsE"] 14, keyed 9 ["TagsB"] 16,
      keyed 10 ["TagsD"] 18, keyed 11 ["TagsC"] 20, keyed 12 ["TagsM"] 22,
      { level := 13, path := ["Fulfilment", "TagsM", "Parts"], repeatability := some 2 },
      keyed 14 ["TagsT"] 25, keyed 15 ["TagsR"] 27, keyed 16 ["TagsN2"] 29,
      { level := 17, path := ["Fulfilment", "TagsN2", "Parts2"], repeatability := some 2 }] }

private def routeRead (groups : List String) (field : String) (model := routeModel)
    (rule : List String := ["Invoices"]) : Verdict :=
  verdict (elaborateNumericComparison model ("Fulfilment" :: rule)
      (gtZero (.field { base := .absolute, groups := "Fulfilment" :: groups, field })))
    numericClass

/- The walk asks the outer level first: below the unkeyed `Ret` the keyed `Sub` is never reached
   (`Rn1a`), and the keyed `Ref` under another name meets the name gate before `Sub2` (`Rn1b`). A key
   of the same name and kind is a legal parallel iteration the Kernel admits and this route refuses
   claiming no class (`Rn3s`); a Number, Enumeration, Boolean or Date key meets the type gate (`Rn3n`,
   `Rn3e`, `Rn3b`, `Rn3d`). -/
example :
    [routeRead ["Ret", "Sub"] "SubAmount", routeRead ["Ref", "Sub2"] "Sub2Amount",
      routeRead ["TagsS"] "TAmount", routeRead ["TagsN"] "TAmount", routeRead ["TagsE"] "TAmount",
      routeRead ["TagsB"] "TAmount", routeRead ["TagsD"] "TAmount"] =
    [noWildcard, some (some .errorFieldInvalidIndex), unclassed] ++
      List.replicate 4 (some (some .errorFieldInvalidIndexType)) := by
  native_decide

/- Keyed by a Number instead, the error field's path meets the String key at the measured type gate
   (the group rows of the index-gate record) and the Enumeration and Date keys too, while no row
   measures a Number key against a Boolean one, so that claims no class
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-25b-index-type-table)). -/
example :
    let numberKeyed : FlatModel :=
      { routeModel with fields := routeModel.fields.map fun field =>
          if field.id == 2 then { field with policy := number } else field }
    [["TagsS"], ["TagsN"], ["TagsE"], ["TagsB"], ["TagsD"]].map (routeRead · "TAmount" numberKeyed) =
    [some (some .errorFieldInvalidIndexType), unclassed, some (some .errorFieldInvalidIndexType),
      unclassed, some (some .errorFieldInvalidIndexType)] := by
  native_decide

/- The peer's type table, the rule's key first
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-25b-index-type-table)). A String key splits from a
   Confirm, DateTime, Time and date-range key; a Date from a date range, a Boolean from a Confirm, a
   Number from an Enumeration and an Enumeration from a Boolean. -/
example :
    [routeRead ["TagsC"] "TAmount", routeRead ["TagsM"] "TAmount", routeRead ["TagsT"] "TAmount",
      routeRead ["TagsR"] "TAmount", routeRead ["TagsR"] "TAmount" (rule := ["TagsD"]),
      routeRead ["TagsC"] "TAmount" (rule := ["TagsB"]), routeRead ["TagsE"] "TAmount" (rule := ["TagsN"]),
      routeRead ["TagsB"] "TAmount" (rule := ["TagsE"])] =
    List.replicate 8 (some (some .errorFieldInvalidIndexType)) := by
  native_decide

/- The pairs the table admits are legal parallel iterations: a Date key beside a DateTime or Time
   one, a DateTime beside a Time, and two Numbers of different scale, each refused here claiming no
   class. Below a legal pair the walk asks the unkeyed level next, as `kf371` measures for one kind;
   that the walk goes on past a pair of two kinds is this project's assumption, which the same read
   from a Time key separates, the reverse pair no row measures stopping the walk. -/
example :
    [routeRead ["TagsM"] "TAmount" (rule := ["TagsD"]), routeRead ["TagsT"] "TAmount" (rule := ["TagsD"]),
      routeRead ["TagsT"] "TAmount" (rule := ["TagsM"]), routeRead ["TagsN2"] "TAmount" (rule := ["TagsN"]),
      routeRead ["TagsM", "Parts"] "PAmount" (rule := ["TagsD"]),
      routeRead ["TagsN2", "Parts2"] "PAmount" (rule := ["TagsN"]),
      routeRead ["TagsM", "Parts"] "PAmount" (rule := ["TagsT"])] =
    List.replicate 4 unclassed ++ [noWildcard, noWildcard, unclassed] := by
  native_decide

/-! ## A computation's target places the class -/

/-- The grid's computation sheet: fixed `Out` and `Ledger`, root fields of three kinds, and a
    repeatable `Batches`, keyed by `BKey` when `keyed`, holding a fixed `Flags` and a repeatable
    `Items`. -/
private def probeModel (keyed : Bool) : FlatModel :=
  let row (id : FieldId) (groups : List String) (name : String) (policy : FieldPolicy)
      (scope : List RepeatableLevel := []) : FlatFieldDecl :=
    { id, groupPath := "Probe" :: groups, name, policy, repeatableScope := scope }
  let range (id : FieldId) (groups : List String) (name : String)
      (scope : List RepeatableLevel := []) : FlatFieldDecl :=
    { row id groups name { kind := .dateRange } scope with
      dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }
  let enum (id : FieldId) (groups : List String) (name : String)
      (scope : List RepeatableLevel := []) : FlatFieldDecl :=
    { row id groups name { kind := .enumeration } scope with
      enumeration := some { storedTokens := ["A", "B"] } }
  { fields := [
      row 1 ["Out"] "Free" number, range 2 ["Out"] "RangeOut", enum 3 ["Out"] "EnumOut",
      row 4 ["Ledger"] "LNote" text, row 5 [] "RootS" text, range 6 [] "RootRange",
      enum 7 [] "RootEnum",
      row 8 ["Batches"] "BKey" text [10], row 9 ["Batches"] "BText" text [10],
      range 10 ["Batches"] "BRange" [10], enum 11 ["Batches"] "BEnum" [10],
      row 12 ["Batches", "Flags"] "F1" { kind := .boolean } [10],
      row 13 ["Batches", "Flags"] "F2" { kind := .boolean } [10],
      row 14 ["Batches", "Items"] "W" number [10, 11], row 15 ["Batches", "Items"] "Q" number [10, 11]]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Batches"], repeatability := some 2,
        indexField := if keyed then some 8 else none },
      { level := 11, path := ["Probe", "Batches", "Items"], repeatability := some 2 }] }

private def pp (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := "Probe" :: groups, field }

private def batchesStar (itemsStarred : Bool) (field : String) : SurfaceStarFieldPath :=
  { base := .absolute, field,
    groups := [{ name := "Probe" }, { name := "Batches", starred := true },
      { name := "Items", starred := itemsStarred }] }

private def batchesText : SurfaceStarFieldPath :=
  { base := .absolute, field := "BText", groups := [{ name := "Probe" }, { name := "Batches", starred := true }] }

private def computationClass : NumericComputationElabError → Option KernelStaticDiagnostic
  | .aggregate (.shape error) => error.diagnostic?
  | .productAggregate error => error.diagnostic?
  | .tokenValueCount (.source error) => error.diagnostic?
  | .booleanValueCount (.shape error) => error.diagnostic?
  | error => error.iterationDiagnostic? <|> error.groupCountDiagnostic?

/-- The grid's nine computations declared in `declaringGroup`, in its column order: the String
    value count plain and starred, the Boolean group count, `SumOfProducts` below a star and fully
    starred, `FirstFilledValue` below a star and fully starred into the Number `Free`, then the
    DateRange and Enumeration `FirstFilledValue` into their own targets. -/
private def computationRow (keyed : Bool) (declaringGroup : List String) : List Verdict :=
  let model := probeModel keyed
  let decl := "Probe" :: declaringGroup
  let numeric (e : AuthoredNumericExpr SurfaceNumericComputationAtom) : Verdict :=
    verdict (elaborateCompleteNumericComputationOperation model decl 1 e) computationClass
  let bText (starred : Bool) : SurfaceProjectedTokenEntityOperand :=
    if starred then .star batchesText .stored else .field (.direct (pp ["Batches"] "BText"))
  let flags : SurfaceGroupReference := .path { base := .absolute, groups := ["Probe", "Batches", "Flags"] }
  [numeric (.atom (.tokenValueCount "x"
      { first := bText false, rest := [.field (.direct (pp [] "RootS"))] })),
    numeric (.atom (.tokenValueCount "x"
      { first := bText true, rest := [.field (.direct (pp [] "RootS"))] })),
    numeric (.atom (.booleanValueCount true { first := .group flags, rest := [] })),
    numeric (.atom (.sumOfProducts { left := batchesStar false "W", right := batchesStar false "Q" })),
    numeric (.atom (.sumOfProducts { left := batchesStar true "W", right := batchesStar true "Q" })),
    numeric (.atom (.firstFilled { first := .star (batchesStar false "W"), rest := [] })),
    numeric (.atom (.firstFilled { first := .star (batchesStar true "W"), rest := [] })),
    verdict (checkDateRangeFirstFilledDirectComputation model decl 2
        { first := .field (pp ["Batches"] "BRange"), rest := [.field (pp [] "RootRange")] })
      fun | .sourceShape error => error.diagnostic? | _ => none,
    verdict (elaborateEnumerationFirstFilledComputation model decl 3
        { first := .field (.direct (pp ["Batches"] "BEnum")),
          rest := [.field (.direct (pp [] "RootEnum"))] })
      fun | .shape error => error.diagnostic? | _ => none]

/- Declared in `Ledger` or in `Batches`, each target lies outside, and every carrier that leaves a
   level unbound draws containment, keyed or not (`L00`, `L02`, `L04`, `L06`, `LR00`, `LE00` and
   their `B` twins); the starred controls are admitted (`L01`, `L07`), except `SumOfProducts`, whose
   own bar refuses a star above the lowest level (`L05`, `B05`). Declared in `Out`, the target's own group, the unbound
   `Batches` draws the missing star, or the index class once keyed, while a level below the first
   star stays the missing star (`O00`–`O07`, `OR00`, `OE00`). -/
example :
    let bar : Verdict := some (some .wildcardOnlyAtLowestLevelAllowed)
    let outside : List Verdict :=
      [containment, none, containment, containment, bar, containment, none, containment, containment]
    [computationRow false ["Ledger"], computationRow false ["Batches"], computationRow true ["Ledger"],
      computationRow true ["Batches"]] = List.replicate 4 outside ∧
    computationRow false ["Out"] =
      [noWildcard, none, noWildcard, noWildcard, bar, noWildcard, none, noWildcard, noWildcard] ∧
    computationRow true ["Out"] =
      [noIndex, none, noIndex, noWildcard, bar, noWildcard, none, noIndex, noIndex] := by
  native_decide

/- The fully starred Boolean group count and Enumeration `FirstFilledValue` are admitted from all
   three groups, keyed or not (`L03`, `B03`, `O03`, `LE01`, `BE01`, `OE01`). -/
example :
    let flagsStar : SurfaceStarGroupPath :=
      { base := .absolute, groups := [{ name := "Probe" }, { name := "Batches", starred := true }, { name := "Flags" }] }
    let enumStar : SurfaceStarFieldPath :=
      { base := .absolute, field := "BEnum", groups := [{ name := "Probe" }, { name := "Batches", starred := true }] }
    [false, true].flatMap (fun keyed => [["Ledger"], ["Batches"], ["Out"]].map fun declaring =>
      let decl := "Probe" :: declaring
      [verdict (elaborateCompleteNumericComputationOperation (probeModel keyed) decl 1
          (.atom (.booleanValueCount true { first := .starredGroup flagsStar, rest := [] }))) computationClass,
        verdict (elaborateEnumerationFirstFilledComputation (probeModel keyed) decl 3
          { first := .star enumStar, rest := [.field (.direct (pp [] "RootEnum"))] })
          fun | .shape error => error.diagnostic? | _ => none]) =
    List.replicate 6 [none, none] := by
  native_decide

end A12Kernel.Conformance.ReadingScope
