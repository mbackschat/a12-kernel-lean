import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: whole-document steps under a presence guard

A DateTime day shift `DTA`, a full-Date copy `DC`, a DateRange construction `DR` and an Enumeration copy
`EC`, each under `FieldFilled(G)`, a full-Date copy `DCN` under `FieldNotFilled(G)`, and a copy `DCC`
under `FieldFilled(NG)` on a computed Number `NG = [N0]`, with a Number reader of each guarded target
authored ahead of it. Every computed target is seeded with a value no row computes. The fixture is the
model of the [guarded-step checkpoint](../../docs/sources/computation-scheduling-probes.md#src-guarded-document-steps),
and every document row is the Kernel's, measured on both codegen strategies.

The rows separate a guard that does not hold, whose step clears and is read as empty, from one that
reads poison, whose step clears and is read as poison. A guard on a computed Number reads its
completion: a malformed `N0` poisons `NG` and so the guard on it, where the filled seed would let the
step run. An absent `N0` copies as `0`, which is filled, so that row cannot tell completion from seed.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanGuarded

open A12Kernel

private def gId : FieldId := 0
private def ngId : FieldId := 1
private def n0Id : FieldId := 2
private def d0Id : FieldId := 3
private def d1Id : FieldId := 4
private def dt0Id : FieldId := 5
private def e0Id : FieldId := 6
private def dcId : FieldId := 7
private def dtaId : FieldId := 8
private def drId : FieldId := 9
private def ecId : FieldId := 10
private def dcnId : FieldId := 11
private def dccId : FieldId := 12
private def ndId : FieldId := 13
private def ndtId : FieldId := 14
private def nrId : FieldId := 15
private def neId : FieldId := 16
private def ndcId : FieldId := 17

private def numberDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Gd"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def dateDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Gd"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }

private def dateTimeDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Gd"]
  name
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full }

private def rangeDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Gd"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }

private def enumerationDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Gd"]
  name
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["1", "2"] }

private def model : FlatModel :=
  { fields := [
      numberDeclaration gId "G", numberDeclaration ngId "NG", numberDeclaration n0Id "N0",
      dateDeclaration d0Id "D0", dateDeclaration d1Id "D1", dateTimeDeclaration dt0Id "DT0",
      enumerationDeclaration e0Id "E0", dateDeclaration dcId "DC", dateTimeDeclaration dtaId "DTA",
      rangeDeclaration drId "DR", enumerationDeclaration ecId "EC", dateDeclaration dcnId "DCN",
      dateDeclaration dccId "DCC", numberDeclaration ndId "ND", numberDeclaration ndtId "NDT",
      numberDeclaration nrId "NR", numberDeclaration neId "NE", numberDeclaration ndcId "NDC"]
    timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberStep? (target : FieldId) (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateNumericTargetComputationTable model ["Gd"] target [(none, expression)]).toOption.map .number

private def guarded? (guard : ComputationCondition) (step : Option (CheckedDocumentComputationStep model)) :
    Option (CheckedScalarComputationStep model) := do
  pure (.document (← (← step).guard? guard))

private def dateCopy? (target : FieldId) : Option (CheckedDocumentComputationStep model) :=
  (elaborateFullDateFieldComputation model d0Id target).toOption.map .ofFullDate

private def dayShift? : Option (CheckedDocumentComputationStep model) := do
  let operation ← (elaborateDateTimeDayShiftComputation model dt0Id (.literal 1) dtaId).toOption
  pure (.ofDateTimeDayShift operation)

private def range? : Option (CheckedDocumentComputationStep model) :=
  (elaborateDateRangeConstructionComputation model ["Gd"] drId d0Id d1Id).toOption.map
    .ofDateRangeConstruction

private def enumerationCopy? : Option (CheckedDocumentComputationStep model) :=
  (elaborateEnumerationComputation model ["Gd"] ecId (.field (.direct (bare "E0")))).toOption.map
    .ofEnumeration

private def filled (field : FieldId) : ComputationCondition := .leaf (.fieldFilled field)

/-- The model's computations in its authored order, every reader ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? ndId (.atom (.temporalFieldPart (bare "DC") (.date .day))),
    numberStep? ndtId (.atom (.temporalFieldPart (bare "DTA") (.time .hour))),
    numberStep? nrId (.atom (.dateRangeBoundPart (bare "DR") .start .day)),
    numberStep? neId (.atom (.fieldValueAsNumber (.direct (bare "EC")))),
    numberStep? ndcId (.atom (.temporalFieldPart (bare "DCC") (.date .day))),
    guarded? (filled gId) (dateCopy? dcId), guarded? (filled gId) dayShift?,
    guarded? (filled gId) range?, guarded? (filled gId) enumerationCopy?,
    guarded? (.leaf (.fieldNotFilled gId)) (dateCopy? dcnId),
    guarded? (filled ngId) (dateCopy? dccId),
    numberStep? ngId (.atom (.field (bare "N0")))].mapM id).get (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

private def dateRaw (text : String) : RawCell :=
  match (certifyFullDateInputField (dateDeclaration d0Id "D0")).toOption with
  | none => .rejected .dateFormat
  | some checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD (.rejected .dateFormat)

private def dateTimeRaw (text : String) : RawCell :=
  match (certifyDateTimeInputField (dateTimeDeclaration dt0Id "DT0")).toOption with
  | none => .rejected .dateFormat
  | some checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD (.rejected .dateFormat)

private def cell (field : FieldId) (text : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text, raw }

private def numberCell (field : FieldId) (amount : Int) : ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

private def malformedNumberCell (field : FieldId) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := "x", raw := .rejected .malformed }

private def rangeRaw (text : String) : RawCell :=
  (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
    { format := "yyyy-MM-dd", separator := "/" } text).toOption.getD (.rejected .dateFormat)

/-- Every computed target seeded with a value no row computes, and the sources every row holds. -/
private def fixed : List ClassifiedCellInput :=
  [dcId, dcnId, dccId].map (fun field => cell field "2000-01-01" (dateRaw "2000-01-01")) ++
    [cell dtaId "2000-01-01T00:00:00" (dateTimeRaw "2000-01-01T00:00:00"),
      cell drId "2000-01-01/2000-01-02" (rangeRaw "2000-01-01/2000-01-02"),
      cell ecId "2" (.parsed (.enum "2"))] ++
    [ndId, ndtId, nrId, neId, ndcId, ngId].map (numberCell · 99) ++
    [cell d0Id "2024-03-10" (dateRaw "2024-03-10"), cell d1Id "2024-04-20" (dateRaw "2024-04-20"),
      cell dt0Id "2024-03-10T10:00:00" (dateTimeRaw "2024-03-10T10:00:00"),
      cell e0Id "1" (.parsed (.enum "1"))]

private def reported : List FieldId :=
  [dcId, dtaId, drId, ecId, dcnId, dccId, ngId, ndId, ndtId, nrId, neId, ndcId]

/-- A computed value, or `-` for one the Kernel reports cleared. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.fullDate (.accepted stored)) => some (target, stored.text)
  | .document target (.dateTime (.accepted stored)) => some (target, stored.text)
  | .document target (.dateRange (.accepted stored)) => some (target, stored.text)
  | .document target (.enumeration (.accepted stored)) => some (target, stored.text)
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _))
  | .document target (.dateTime .noValue) | .document target (.dateTime (.poison _))
  | .document target (.dateRange .noValue) | .document target (.dateRange (.poison _))
  | .document target (.enumeration .noValue) | .document target (.enumeration (.poison _)) =>
      some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.fullDate (.errored _ _)) | .document _ (.dateTime (.errored _ _))
  | .document _ (.dateRange (.errored _ _)) | .document _ (.enumeration (.errored _ _))
  | .document _ (.time _) | .document _ (.boolean _) => none

private def values? (cells : List ClassifiedCellInput) : Option (List String) := do
  let input ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := fixed ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

/- Row `s01`: the guard holds, so every guarded step computes from the fresh sources and its reader reads
it, while the `FieldNotFilled` copy clears. -/
example : values? [numberCell gId 1, numberCell n0Id 1] =
    some ["2024-03-10", "2024-03-11T10:00:00", "2024-03-10/2024-04-20", "1", "-", "2024-03-10", "1",
      "10", "10", "10", "1", "10"] := by
  native_decide

/- Rows `s02` and `s03`: an absent guard clears every `FieldFilled` step, read as empty, and runs the
`FieldNotFilled` copy; a malformed one clears both kinds and every reader, read as poison. -/
example :
    values? [numberCell n0Id 1] =
      some ["-", "-", "-", "-", "2024-03-10", "2024-03-10", "1", "0", "0", "0", "0", "10"] ∧
    values? [malformedNumberCell gId, numberCell n0Id 1] =
      some ["-", "-", "-", "-", "-", "2024-03-10", "1", "-", "-", "-", "-", "10"] := by
  native_decide

/- Rows `s04` and `s05`: the guard on `NG` reads its completion, so an absent `N0` copied as `0` is
filled and `DCC` computes, while a malformed `N0` poisons `NG`, `DCC` and its reader. -/
example :
    values? [] =
      some ["-", "-", "-", "-", "2024-03-10", "2024-03-10", "0", "0", "0", "0", "0", "10"] ∧
    values? [numberCell gId 1, malformedNumberCell n0Id] =
      some ["2024-03-10", "2024-03-11T10:00:00", "2024-03-10/2024-04-20", "1", "-", "-", "-",
        "10", "10", "10", "1", "-"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanGuarded
