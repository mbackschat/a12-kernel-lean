import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.TimeComputation

/-! # Authored scalar plan locks: full-Date, Time and Enumeration steps at a join

A full-Date copy `DC = [D0]`, a chained copy `DC2 = [DC]`, a copy `DCG = [D0]` into a target that refuses
dates before 1900, the Time constructions `TC = Time(HoursFromTime(T0), MinutesFromTime(T0))` and
`TC2 = Time(NH, MinutesFromTime(T0))` over a computed Number `NH`, and the Enumeration copies `EC = [E0]`
and `EC2 = [EC]` are whole-document steps of one authored plan. Number computations read them through
`DifferenceInDays`, `HoursFromTime`, `FieldValueAsNumber`, and the two fill guards. The fixture is the second
model of the
[whole-document join checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-document-step-join).
Every document row is the Kernel's, measured on both codegen strategies; a row of the first grid reports
only the fields that grid's model declares.
-/

namespace A12Kernel.Conformance.ScalarComputationPlanDocument

open A12Kernel

private def d0Id : FieldId := 0
private def dcId : FieldId := 1
private def dc2Id : FieldId := 2
private def dcgId : FieldId := 3
private def e0Id : FieldId := 4
private def ecId : FieldId := 5
private def ec2Id : FieldId := 6
private def n0Id : FieldId := 7
private def ndId : FieldId := 8
private def nd2Id : FieldId := 9
private def ndgId : FieldId := 10
private def kdgId : FieldId := 11
private def kndgId : FieldId := 12
private def neId : FieldId := 13
private def ne2Id : FieldId := 14
private def keId : FieldId := 15
private def kneId : FieldId := 16
private def t0Id : FieldId := 17
private def tcId : FieldId := 18
private def tc2Id : FieldId := 19
private def ntId : FieldId := 20
private def nhId : FieldId := 21
private def nt2Id : FieldId := 22

private def dateDeclaration (id : FieldId) (name : String) (youngerThan1900Check := false) :
    FlatFieldDecl where
  id
  groupPath := ["Fam"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy :=
    some { format := "dd.MM.yyyy", partialMode := .full, youngerThan1900Check }

private def timeDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Fam"]
  name
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }

private def enumerationDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Fam"]
  name
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["1", "2"] }

private def numberDeclaration (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := ["Fam"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

/-- The hour Number `TC2` reads, declared as the Kernel model declares it: a component needs a
nonnegative scale-0 domain bounded by the hour's maximum. -/
private def hourDeclaration : FlatFieldDecl :=
  { numberDeclaration nhId "NH" with
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxIntegerDigits := some 2, minimum := some 0, maximum := some 23 } }

private def model : FlatModel :=
  { fields := [
      dateDeclaration d0Id "D0", dateDeclaration dcId "DC", dateDeclaration dc2Id "DC2",
      dateDeclaration dcgId "DCG" (youngerThan1900Check := true),
      enumerationDeclaration e0Id "E0", enumerationDeclaration ecId "EC",
      enumerationDeclaration ec2Id "EC2",
      numberDeclaration n0Id "N0", numberDeclaration ndId "ND", numberDeclaration nd2Id "ND2",
      numberDeclaration ndgId "NDG", numberDeclaration kdgId "KDG", numberDeclaration kndgId "KNDG",
      numberDeclaration neId "NE", numberDeclaration ne2Id "NE2", numberDeclaration keId "KE",
      numberDeclaration kneId "KNE", timeDeclaration t0Id "T0", timeDeclaration tcId "TC",
      timeDeclaration tc2Id "TC2", numberDeclaration ntId "NT", hourDeclaration,
      numberDeclaration nt2Id "NT2"]
    timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberStep? (target : FieldId) (guard : Option ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateNumericTargetComputationTable model ["Fam"] target [(guard, expression)]).toOption.map
    .number

private def dateCopy? (source target : FieldId) : Option (CheckedScalarComputationStep model) :=
  (elaborateFullDateFieldComputation model source target).toOption.map
    fun operation => .document (.ofFullDate operation)

private def enumerationCopy? (source : String) (target : FieldId) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateEnumerationComputation model ["Fam"] target (.field (.direct (bare source)))).toOption.map
    fun operation => .document (.ofEnumeration operation)

private def timeConstruction? (components : SurfaceTimeComponents) (target : FieldId) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateTimeConstructionComputation model components target).toOption.map
    fun operation => .document (.ofTimeConstruction operation)

private def hours (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (bare field) (.time .hour))

private def days (left right : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dayDifference (.field (bare left)) (.field (bare right)))

private def asNumber (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber (.direct (bare field)))

private def n0 : AuthoredNumericExpr SurfaceNumericAtom := .atom (.field (bare "N0"))

/-- The model's computations in its authored order: every reader ahead of what it reads. -/
private def authored : List (CheckedScalarComputationStep model) :=
  ([numberStep? ndId none (days "D0" "DC"), numberStep? neId none (asNumber "EC"),
    numberStep? keId (some (.fieldFilled ecId)) n0,
    numberStep? kneId (some (.fieldNotFilled ecId)) n0,
    dateCopy? d0Id dcId, enumerationCopy? "E0" ecId,
    dateCopy? dcId dc2Id, dateCopy? d0Id dcgId,
    numberStep? ndgId none (days "D0" "DCG"),
    numberStep? kdgId (some (.fieldFilled dcgId)) n0,
    numberStep? kndgId (some (.fieldNotFilled dcgId)) n0,
    numberStep? nd2Id none (days "D0" "DC2"),
    enumerationCopy? "EC" ec2Id, numberStep? ne2Id none (asNumber "EC2"),
    numberStep? ntId none (hours "TC"),
    timeConstruction? (.minute (.extractor .hour t0Id) (.extractor .minute t0Id)) tcId,
    numberStep? nhId none (hours "T0"),
    timeConstruction? (.minute (.number nhId) (.extractor .minute t0Id)) tc2Id,
    numberStep? nt2Id none (hours "TC2")].mapM id).get
    (by native_decide)

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan authored).toOption.get (by native_decide)

/-- The raw cell the Date declaration classifies `text` into in the model's zone. -/
private def dateRaw (text : String) : RawCell :=
  match (certifyFullDateInputField (dateDeclaration d0Id "D0")).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

/-- The raw cell the Time declaration classifies `text` into in the model's zone. -/
private def timeRaw (text : String) : RawCell :=
  match (certifyTimeInputField (timeDeclaration t0Id "T0")).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def timeCell (field : FieldId) (text : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text, raw := timeRaw text }

private def dateCell (field : FieldId) (text : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := text, raw := dateRaw text }

private def tokenCell (field : FieldId) (token : String) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored := token, raw := .parsed (.enum token) }

/-- A Number cell classified by its own declaration, so the Kernel's out-of-range seed `99` for `NH`
is formally invalid here as it is there. -/
private def numberCell (field : FieldId) (amount : Int) : ClassifiedCellInput :=
  let decimal : NumericInputDecimal := { unscaled := amount, scale := 0 }
  { address := { field, path := [] }
    stored := toString amount
    raw := match model.lookupUniqueId field with
      | .ok { policy := { kind := .number info .. }, numericTargetConstraints, .. } =>
          numericTargetConstraints.classifyFormalRead info (.decimal decimal)
      | _ => .parsed (.num amount)
    numericDecimal := some decimal }

/-- Every computed target seeded as the Kernel rows were, so a stale read would show, except the Time
targets: the Kernel's `00:00:00` would read as the `0` an absent `T0` also gives, so `01:01:01` stands in. -/
private def seeds : List ClassifiedCellInput :=
  [ndId, nd2Id, ndgId, kdgId, kndgId, neId, ne2Id, keId, kneId, ntId, nhId, nt2Id].map
      (numberCell · 99) ++
    [dcId, dc2Id, dcgId].map (dateCell · "01.01.2000") ++ [ecId, ec2Id].map (tokenCell · "2") ++
    [tcId, tc2Id].map (timeCell · "01:01:01")

/-- A computed value, `E` for a target the Kernel retains as errored, or `-` for one it clears. -/
private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.fullDate (.accepted stored)) => some (target, stored.text)
  | .document target (.fullDate (.errored _ _)) => some (target, "E")
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _)) =>
      some (target, "-")
  | .document target (.time (.accepted stored)) => some (target, stored.text)
  | .document target (.time .noValue) | .document target (.time (.poison _)) => some (target, "-")
  | .document target (.enumeration (.accepted stored)) => some (target, stored.text)
  | .document target (.enumeration .noValue) | .document target (.enumeration (.poison _)) =>
      some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.dateTime _) | .document _ (.enumeration (.errored _ _)) => none

private def values? (reported : List FieldId) (cells : List ClassifiedCellInput) :
    Option (List String) := do
  let input ← (checkDocument prepared "en_US"
    { instantiatedRows := [], cells := seeds ++ cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  reported.mapM fun target => (found.find? (·.1 == target)).map (·.2)

private def dateFields : List FieldId := [dcId, dc2Id, dcgId, ndId, nd2Id, ndgId, kdgId, kndgId]
private def enumerationFields : List FieldId := [ecId, ec2Id, neId, ne2Id, keId, kneId]
private def firstGridFields : List FieldId := [dcId, ndId, ecId, neId, keId, kneId]

private def timeFields : List FieldId := [tcId, ntId, nhId, tc2Id, nt2Id]

private def inputs (d0 : Option ClassifiedCellInput := some (dateCell d0Id "10.03.2024"))
    (e0 : Option ClassifiedCellInput := some (tokenCell e0Id "1"))
    (t0 : Option ClassifiedCellInput := some (timeCell t0Id "10:30:45")) : List ClassifiedCellInput :=
  [d0, e0, t0, some (numberCell n0Id 5)].filterMap id

/- Every source readable, row `g01`: each copy and chained copy is read fresh, so every difference is
`0`, both filled guards fire and neither unfilled one does. -/
example :
    values? dateFields inputs =
      some ["10.03.2024", "10.03.2024", "10.03.2024", "0", "0", "0", "5", "-"] ∧
    values? enumerationFields inputs = some ["1", "1", "1", "1", "5", "-"] := by
  native_decide

/- Row `g02`: a pre-1900 Date copies unchanged into the plain targets, while the guarded target retains it
as errored and its readers see poison, so the difference and both guards clear. Reading the retained text
would give `0` and fire the filled guard; reading it as empty would fire the unfilled one. -/
example :
    values? dateFields (inputs (d0 := some (dateCell d0Id "31.12.1899"))) =
      some ["31.12.1899", "31.12.1899", "E", "0", "0", "-", "-", "-"] := by
  native_decide

/- Row `g05` and the first grid's `f02`: an absent Date clears every copy, and each cleared copy reads
empty, so the differences are `0` and only the unfilled guard fires; a malformed Date poisons the copy
and its difference instead. -/
example :
    values? dateFields (inputs (d0 := none)) =
      some ["-", "-", "-", "0", "0", "0", "-", "5"] ∧
    values? firstGridFields (inputs (d0 := some (dateCell d0Id "bad"))) =
      some ["-", "-", "1", "1", "5", "-"] := by
  native_decide

/- Rows `g03`, `g06` and the first grid's `f04`. The Kernel reports no outcome for `EC` and `EC2` on
`g03`, whose seed `2` is the value computed, which `NE` and `NE2` confirm. A token outside the domain
poisons the copy, the chained copy and every reader; an absent one clears the copy, which reads empty. -/
example :
    values? enumerationFields (inputs (e0 := some (tokenCell e0Id "2"))) =
      some ["2", "2", "2", "2", "5", "-"] ∧
    values? enumerationFields (inputs (e0 := some (tokenCell e0Id "3"))) =
      some ["-", "-", "-", "-", "-", "-"] ∧
    values? firstGridFields (inputs (e0 := none)) =
      some ["10.03.2024", "0", "-", "0", "-", "5"] := by
  native_decide

/- Rows `g01` and `g04`: each construction drops the seconds, `NT` and `NT2` read the constructed clock
rather than the seed `01:01:01`, and `TC2` reads the computed Number `NH`. -/
example :
    values? timeFields inputs = some ["10:30:00", "10", "10", "10:30:00", "10"] ∧
    values? timeFields (inputs (t0 := some (timeCell t0Id "23:59:59"))) =
      some ["23:59:00", "23", "23", "23:59:00", "23"] := by
  native_decide

/- Row `g07` and the first grid's `f07`: a malformed Time poisons both constructions and every reader of
them, while an absent one clears the construction, which its reader sees as empty and reads as `0`. -/
example :
    values? timeFields (inputs (t0 := some (timeCell t0Id "bad"))) =
      some ["-", "-", "-", "-", "-"] ∧
    values? [tcId, ntId] (inputs (t0 := none)) = some ["-", "0"] := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanDocument
