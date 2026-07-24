import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Semantics.DateTimeDayDifference

/-! # Numeric-computation conformance support

Shared declarations, checked contexts, and expression constructors used by at least two focused numeric-computation conformance modules.
-/

namespace A12Kernel.Conformance.NumericComputation.Support

open A12Kernel

def sourceId : FieldId := 0
def laterId : FieldId := 1

def numberInfo : NumField := { scale := 0, signed := true }

def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .number numberInfo }

def stringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .string }

def source : FlatFieldDecl :=
  numberDeclaration sourceId "Source"

def later : FlatFieldDecl :=
  numberDeclaration laterId "Later"

def targetId : FieldId := 2

def target : FlatFieldDecl :=
  { numberDeclaration targetId "Target" with
    numericTargetConstraints := { zeroAllowed := false } }

def wrongId : FieldId := 3
def repeatedId : FieldId := 4
def timeId : FieldId := 5
def dateTimeId : FieldId := 6
def dateId : FieldId := 7
def enumerationId : FieldId := 8
def numericStringId : FieldId := 9
def hostDigitEnumerationId : FieldId := 11
def productRightId : FieldId := 12
def laterDateTimeId : FieldId := 13
def repeatedTokenId : FieldId := 14

def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

def dateTimeComponents : TemporalComponents :=
  { TemporalComponents.fullDate with
    hour := true, minute := true, second := true }

def temporalDeclaration (id : FieldId) (name : String)
    (kind : TemporalKind) (components : TemporalComponents) : FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .temporal kind components }

def wrong : FlatFieldDecl :=
  stringDeclaration wrongId "Wrong"

def numericString : FlatFieldDecl :=
  { (stringDeclaration numericStringId "NumericCode") with
    stringPatternSource := some "[0-9]+"
    stringPolicy := { maxLength := some 15 } }

def repeated : FlatFieldDecl :=
  { id := repeatedId
    groupPath := ["Root", "Rows"]
    name := "Repeated"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

def productRight : FlatFieldDecl :=
  { id := productRightId
    groupPath := ["Root", "Rows"]
    name := "ProductRight"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

def repeatedToken : FlatFieldDecl :=
  { id := repeatedTokenId
    groupPath := ["Root", "Rows"]
    name := "Token"
    policy := { kind := .string }
    repeatableScope := [10] }

def model : FlatModel :=
  { fields := [source, later, target, wrong, repeated,
      temporalDeclaration timeId "Time" .time timeComponents,
      temporalDeclaration dateTimeId "DateTime" .dateTime dateTimeComponents,
      temporalDeclaration dateId "Date" .date TemporalComponents.fullDate,
      temporalDeclaration laterDateTimeId "LaterDateTime" .dateTime
        dateTimeComponents,
      numericString, productRight, repeatedToken,
      { id := enumerationId
        groupPath := ["Root"]
        name := "NumericChoice"
        policy := { kind := .enumeration }
        enumeration := some {
          storedTokens := ["-150", "2", "03"]
          categories := [
            { name := "Factor", tokens := ["5", "225", "3"] },
            { name := "Fraction", tokens := [".5", "2.25", "3"] }] } },
      { id := hostDigitEnumerationId
        groupPath := ["Root"]
        name := "HostDigitChoice"
        policy := { kind := .enumeration }
        enumeration := some { storedTokens := ["１２", "-３"] } }]
    repeatableGroups := [{ level := 10, path := ["Root", "Rows"] }]
    baseYear := some 2020 }

def noBaseYearModel : FlatModel := { model with baseYear := none }
def berlinModel : FlatModel := { model with timeZoneId := "Europe/Berlin" }
def unsupportedZoneModel : FlatModel :=
  { model with timeZoneId := "Pacific/Apia" }

def boundedScaleTwoTargetId : FieldId := 20

def boundedScaleTwoTarget : FlatFieldDecl :=
  { id := boundedScaleTwoTargetId
    groupPath := ["Root"]
    name := "BoundedScaleTwoTarget"
    policy := { kind := .number { scale := 2, signed := true } }
    numericTargetConstraints := {
      minFractionalDigits := 2
      maximum := some 5 } }

def boundedScaleTwoModel : FlatModel :=
  { fields := [boundedScaleTwoTarget] }

def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

def surfacePath (groups : List String) (name : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

def surfaceField (groups : List String) (name : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (surfacePath groups name))

def surfaceStringRange (start finish : Nat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.stringRange (surfacePath ["Root"] "Wrong") start finish)

def surfaceFieldValueAsNumber
    (source : SurfaceTextFieldOperand :=
      .direct (surfacePath ["Root"] "NumericChoice")) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber source)

def surfaceAggregate (op : NumericAggregateOp) (first : String)
    (rest : List String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.aggregate op {
    first := surfacePath ["Root"] first
    rest := rest.map (surfacePath ["Root"]) })

def repeatedStarPath : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Root" },
      { name := "Rows", starred := true }]
    field := "Repeated" }

def productRightStarPath : SurfaceStarFieldPath :=
  { repeatedStarPath with field := "ProductRight" }

def surfaceProductAggregate :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.sumOfProducts {
    left := repeatedStarPath
    right := productRightStarPath })

def surfaceFirstFilled
    (first : SurfaceNumberEntityOperand)
    (rest : List SurfaceNumberEntityOperand) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.firstFilled { first, rest })

def surfaceValueCount (expected : Rat)
    (first : SurfaceNumberEntityOperand)
    (rest : List SurfaceNumberEntityOperand) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.valueCount expected { first, rest })

def repeatedAggregateHaving (outerField : String := "Source") :
    SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner
      field := surfacePath ["Root", "Rows"] "Repeated" }
    { origin := .outer
      field := surfacePath ["Root"] outerField }

def surfaceRepeatableAggregate (op : NumericAggregateOp)
    (outerField : String := "Source") :
    AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
  .atom (.aggregate op {
    first := .starHaving repeatedStarPath (repeatedAggregateHaving outerField)
    rest := [] })

def surfaceRepeatableFirstFilled
    (outerField : String := "Source") :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  surfaceFirstFilled
    (.starHaving repeatedStarPath (repeatedAggregateHaving outerField)) []

def surfaceRepeatableValueCount (expected : Rat)
    (outerField : String := "Source") :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  surfaceValueCount expected
    (.starHaving repeatedStarPath (repeatedAggregateHaving outerField)) []

def repeatedTokenStarPath : SurfaceStarFieldPath :=
  { repeatedStarPath with field := "Token" }

def surfaceTokenValueCount (expected : String)
    (first : SurfaceTokenValueCountOperand)
    (rest : List SurfaceTokenValueCountOperand) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.tokenValueCount expected { first, rest })

def surfaceRepeatableTokenValueCount
    (expected : String) (outerField : String := "Source") :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  surfaceTokenValueCount expected
    (.starHaving repeatedTokenStarPath .stored
      (repeatedAggregateHaving outerField)) []

def surfaceBaseYear : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom .baseYear

def surfaceFixedGroupCount :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount [
    .path { base := .absolute, groups := ["Root", "Details"] },
    .path { base := .absolute, groups := ["Root", "Preferences"] }])

def surfaceBaseYearDatePart (source : BaseYearDateSource)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.baseYearDatePart source part)

def surfaceDateFieldPart (name : String) (part : DateNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.date part))

def surfaceTimeFieldPart (name : String) (part : TimeNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.time part))

def surfaceDateDifference (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateDifference unit left right)

def surfaceDateTimeDifference (unit : DateTimeDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateTimeDifference unit left right)

def surfaceDayDifference
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dayDifference left right)

def surfaceDateOperand (name : String) : SurfaceDateDifferenceOperand :=
  .field (surfacePath ["Root"] name)

def checkedErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (target : FieldId := targetId)
    (suppressExactScaleWarning : Bool := false) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] target expression
      suppressExactScaleWarning with
  | .ok _ => none
  | .error error => some error

def noBaseYearErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation noBaseYearModel ["Root"] targetId
      expression with
  | .ok _ => none
  | .error error => some error

def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number numberInfo } raw

def checkedTemporal (kind : TemporalKind) (components : TemporalComponents)
    (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .temporal kind components } raw

def context (source later : CheckedCell := checkedNumber .empty)
    (time : CheckedCell := checkedTemporal .time timeComponents .empty)
    (dateTime : CheckedCell :=
      checkedTemporal .dateTime dateTimeComponents .empty)
    (date : CheckedCell :=
      checkedTemporal .date TemporalComponents.fullDate .empty)
    (code : CheckedCell := formalCheck { kind := .string } .empty)
    (choice : CheckedCell := formalCheck { kind := .enumeration } .empty)
    (numericCode : CheckedCell := numericString.checkRaw .empty)
    (hostDigitChoice : CheckedCell :=
      formalCheck { kind := .enumeration } .empty)
    (laterDateTime : CheckedCell :=
      checkedTemporal .dateTime dateTimeComponents .empty) :
    ScalarComputationContext where
  read field :=
    if field == sourceId then source
    else if field == laterId then later
    else if field == timeId then time
    else if field == dateTimeId then dateTime
    else if field == dateId then date
    else if field == wrongId then code
    else if field == enumerationId then choice
    else if field == numericStringId then numericCode
    else if field == hostDigitEnumerationId then hostDigitChoice
    else if field == laterDateTimeId then laterDateTime
    else checkedNumber .empty

def repeatableDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

def repeatableCheckedRead (root : CheckedCell)
    (rows : RowIndex → CheckedCell) (environment : Env)
    (field : FieldId) : CheckedCell :=
  if field == sourceId then root
  else if field == repeatedId then
    match environment with
    | [(10, row)] => rows row
    | _ => malformedCheckedCell
  else if field == productRightId then
    match environment with
    | [(10, 1)] => checkedNumber (.parsed (.num 2))
    | [(10, 2)] => checkedNumber (.parsed (.num 4))
    | [(10, 3)] => checkedNumber (.parsed (.num 6))
    | [(10, _)] => checkedNumber .empty
    | _ => malformedCheckedCell
  else if field == repeatedTokenId then
    match environment with
    | [(10, row)] => rows row
    | _ => malformedCheckedCell
  else
    malformedCheckedCell

def cells3 (first second third : CheckedCell) : RowIndex → CheckedCell
  | 1 => first
  | 2 => second
  | 3 => third
  | _ => checkedNumber .empty

def numberCells3 (first second third : RawCell) : RowIndex → CheckedCell :=
  cells3 (checkedNumber first) (checkedNumber second) (checkedNumber third)

def emptyNumberRows : RowIndex → CheckedCell :=
  numberCells3 .empty .empty .empty

def repeatableContext (root : CheckedCell)
    (rows : RowIndex → CheckedCell) : NumericComputationEvaluationContext :=
  { scalar := context root
    document := repeatableDocument [1, 2, 3]
    outer := []
    filterRead := repeatableCheckedRead root rows
    starRead := repeatableCheckedRead root rows }

def firstFilledContext (root : CheckedCell)
    (filterRows targetRows : RowIndex → CheckedCell)
    (later : CheckedCell := checkedNumber .empty)
    (rows : List RowIndex := [1, 2, 3]) :
    NumericComputationEvaluationContext :=
  { scalar := context root later
    document := repeatableDocument rows
    outer := []
    filterRead := repeatableCheckedRead root filterRows
    starRead := repeatableCheckedRead root targetRows }

def instant : Instant := { epochMillis := 1719292867000 }

def dateParts : DateParts := { year := 2024, month := 6, day := 25 }

def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

def dateTimeValue : Value :=
  .temporal (.dateTime instant dateParts clock .storedGregorian)

def dateTimeValueAt (epochMillis : Int) : Value :=
  .temporal (.dateTime { epochMillis } dateParts clock .storedGregorian)

def localDateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

def berlinDateTimeValue
    (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome)
    (resolved :
      (EuropeBerlinLegacyProfile.resolveLocal?
        (localDateTime year month day hour minute second admissible)).isSome) :
    Value :=
  let point := localDateTime year month day hour minute second admissible
  .temporal (.dateTime
    ((EuropeBerlinLegacyProfile.resolveLocal?
      (localDateTime year month day hour minute second admissible)).get resolved)
    point.date.civil.parts point.time .storedGregorian)

def berlinDaylightFoldValue : Value :=
  let point := localDateTime 2024 10 27 2 15 0 (by native_decide)
  let beforeFold := localDateTime 2024 10 27 1 15 0 (by native_decide)
  let daylightInstant :=
    (EuropeBerlinLegacyProfile.resolveLocal? beforeFold).get
      (by native_decide) |>.shiftHours 1
  .temporal (.dateTime daylightInstant point.date.civil.parts point.time
    .storedGregorian)

def dateValue (year : Int) (month day : Nat)
    (basis : DateCalendarBasis := .storedGregorian) : Value :=
  .temporal (.date instant { year, month, day } basis)

def checkedResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

def checkedResultOfIn
    (sourceModel : FlatModel)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation
      sourceModel ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

def checkedErrorOfIn
    (sourceModel : FlatModel)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation
      sourceModel ["Root"] targetId expression with
  | .ok _ => none
  | .error error => some error

def checkedFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) : Option NumericComputationFault :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate input with
      | .ok _ => none
      | .error fault => some fault

def targetPolicy : NumericTargetPolicy where
  info := numberInfo
  minFractionalDigits := 0
  minLeMax := by decide

def checkedTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool)
    (policy : NumericTargetPolicy := targetPolicy)
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression
      suppressExactScaleWarning with
  | .error _ => none
  | .ok checked =>
      match checked.attachTargetPolicy policy with
      | .error _ => none
      | .ok targetChecked => targetChecked.evaluate input |>.toOption

def checkedDeclaredTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult :=
  match elaborateNumericTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

def checkedBoundedScaleTwoTargetResultOf
    (value : Rat) : Option NumericTargetCheckResult :=
  match elaborateNumericTargetComputationOperation
      boundedScaleTwoModel ["Root"] boundedScaleTwoTargetId
      (.literal { value, authoredScale := 2 }) with
  | .error _ => none
  | .ok checked => checked.evaluate context |>.toOption

def checkedRepeatableResultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationResult :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

def checkedRepeatableFaultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationFault :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateIn input with
      | .ok _ => none
      | .error fault => some fault

def checkedRepeatableScalarFaultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : ScalarComputationContext := context) :
    Option NumericComputationFault :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate input with
      | .ok _ => none
      | .error fault => some fault

def checkedRepeatableTargetResultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : NumericComputationEvaluationContext) :
    Option NumericTargetCheckResult :=
  match elaborateNumberEntityTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

def checkedRepeatableErrorOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource)) :
    Option NumericComputationElabError :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .ok _ => none
  | .error error => some error

def checkedCompleteResultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationResult :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

def checkedCompleteScalarResultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

def checkedCompleteErrorOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option NumericComputationElabError :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .ok _ => none
  | .error error => some error

def checkedCompleteFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationFault :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateIn input with
      | .ok _ => none
      | .error fault => some fault

def checkedCompleteScalarFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option NumericComputationFault :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate context with
      | .ok _ => none
      | .error fault => some fault

def checkedCompleteTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : NumericComputationEvaluationContext) :
    Option NumericTargetCheckResult :=
  match elaborateCompleteNumericTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

def targetPolicyAttachErrorOf (policy : NumericTargetPolicy) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] targetId
      (.literal { value := 0, authoredScale := 0 }) with
  | .error error => some error
  | .ok checked =>
      match checked.attachTargetPolicy policy with
      | .error error => some error
      | .ok _ => none

def literal (value : Rat) (authoredScale : Int := 0) :
    AuthoredNumericExpr FlatFieldDecl :=
  .literal { value, authoredScale }

def field (declaration : FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .atom declaration

def divide (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary .divide left right

def binary (op : NumericScaleBinaryOp)
    (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary op left right

def rounded (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .round .halfUp omittedRoundingPlaces body

def absolute (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .abs body

def power (base exponent : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .power base exponent

def resultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  (expression.evaluateComputation input).toOption

def faultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationFault :=
  match expression.evaluateComputation input with
  | .ok _ => none
  | .error fault => some fault

end A12Kernel.Conformance.NumericComputation.Support
