import A12Kernel.Elaboration.NumericComputation

/-! # Numeric computation-expression outcome locks -/

namespace A12Kernel.Conformance.NumericComputation

open A12Kernel

private def sourceId : FieldId := 0
private def laterId : FieldId := 1

private def numberInfo : NumField := { scale := 0, signed := true }

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .number numberInfo }

private def stringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .string }

private def source : FlatFieldDecl :=
  numberDeclaration sourceId "Source"

private def later : FlatFieldDecl :=
  numberDeclaration laterId "Later"

private def targetId : FieldId := 2

private def target : FlatFieldDecl :=
  { numberDeclaration targetId "Target" with
    numericTargetConstraints := { zeroAllowed := false } }

private def wrongId : FieldId := 3
private def repeatedId : FieldId := 4
private def timeId : FieldId := 5
private def dateTimeId : FieldId := 6
private def dateId : FieldId := 7
private def enumerationId : FieldId := 8
private def numericStringId : FieldId := 9
private def hostDigitEnumerationId : FieldId := 11
private def productRightId : FieldId := 12

private def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

private def dateTimeComponents : TemporalComponents :=
  { TemporalComponents.fullDate with
    hour := true, minute := true, second := true }

private def temporalDeclaration (id : FieldId) (name : String)
    (kind : TemporalKind) (components : TemporalComponents) : FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .temporal kind components }

private def wrong : FlatFieldDecl :=
  stringDeclaration wrongId "Wrong"

private def numericString : FlatFieldDecl :=
  { (stringDeclaration numericStringId "NumericCode") with
    stringPatternSource := some "[0-9]+"
    stringPolicy := { maxLength := some 15 } }

private def repeated : FlatFieldDecl :=
  { id := repeatedId
    groupPath := ["Root", "Rows"]
    name := "Repeated"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

private def productRight : FlatFieldDecl :=
  { id := productRightId
    groupPath := ["Root", "Rows"]
    name := "ProductRight"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [source, later, target, wrong, repeated,
      temporalDeclaration timeId "Time" .time timeComponents,
      temporalDeclaration dateTimeId "DateTime" .dateTime dateTimeComponents,
      temporalDeclaration dateId "Date" .date TemporalComponents.fullDate,
      numericString, productRight,
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

private def noBaseYearModel : FlatModel := { model with baseYear := none }

private def boundedScaleTwoTargetId : FieldId := 20

private def boundedScaleTwoTarget : FlatFieldDecl :=
  { id := boundedScaleTwoTargetId
    groupPath := ["Root"]
    name := "BoundedScaleTwoTarget"
    policy := { kind := .number { scale := 2, signed := true } }
    numericTargetConstraints := {
      minFractionalDigits := 2
      maximum := some 5 } }

private def boundedScaleTwoModel : FlatModel :=
  { fields := [boundedScaleTwoTarget] }

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def surfacePath (groups : List String) (name : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

private def surfaceField (groups : List String) (name : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (surfacePath groups name))

private def surfaceStringRange (start finish : Nat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.stringRange (surfacePath ["Root"] "Wrong") start finish)

private def surfaceFieldValueAsNumber
    (source : SurfaceTextFieldOperand :=
      .direct (surfacePath ["Root"] "NumericChoice")) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber source)

private def surfaceAggregate (op : NumericAggregateOp) (first : String)
    (rest : List String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.aggregate op {
    first := surfacePath ["Root"] first
    rest := rest.map (surfacePath ["Root"]) })

private def repeatedStarPath : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Root" },
      { name := "Rows", starred := true }]
    field := "Repeated" }

private def productRightStarPath : SurfaceStarFieldPath :=
  { repeatedStarPath with field := "ProductRight" }

private def surfaceProductAggregate :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.sumOfProducts {
    left := repeatedStarPath
    right := productRightStarPath })

private def repeatedAggregateHaving (outerField : String := "Source") :
    SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner
      field := surfacePath ["Root", "Rows"] "Repeated" }
    { origin := .outer
      field := surfacePath ["Root"] outerField }

private def surfaceRepeatableAggregate (op : NumericAggregateOp)
    (outerField : String := "Source") :
    AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
  .atom (.aggregate op {
    first := .starHaving repeatedStarPath (repeatedAggregateHaving outerField)
    rest := [] })

private def surfaceBaseYear : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom .baseYear

private def surfaceFixedGroupCount :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount [
    .path { base := .absolute, groups := ["Root", "Details"] },
    .path { base := .absolute, groups := ["Root", "Preferences"] }])

private def surfaceBaseYearDatePart (source : BaseYearDateSource)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.baseYearDatePart source part)

private def surfaceDateFieldPart (name : String) (part : DateNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.date part))

private def surfaceTimeFieldPart (name : String) (part : TimeNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.time part))

private def surfaceDateDifference (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateDifference unit left right)

private def surfaceDateOperand (name : String) : SurfaceDateDifferenceOperand :=
  .field (surfacePath ["Root"] name)

private def checkedErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (target : FieldId := targetId)
    (suppressExactScaleWarning : Bool := false) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] target expression
      suppressExactScaleWarning with
  | .ok _ => none
  | .error error => some error

private def noBaseYearErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation noBaseYearModel ["Root"] targetId
      expression with
  | .ok _ => none
  | .error error => some error

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number numberInfo } raw

private def checkedTemporal (kind : TemporalKind) (components : TemporalComponents)
    (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .temporal kind components } raw

private def context (source later : CheckedCell := checkedNumber .empty)
    (time : CheckedCell := checkedTemporal .time timeComponents .empty)
    (dateTime : CheckedCell :=
      checkedTemporal .dateTime dateTimeComponents .empty)
    (date : CheckedCell :=
      checkedTemporal .date TemporalComponents.fullDate .empty)
    (code : CheckedCell := formalCheck { kind := .string } .empty)
    (choice : CheckedCell := formalCheck { kind := .enumeration } .empty)
    (numericCode : CheckedCell := numericString.checkRaw .empty)
    (hostDigitChoice : CheckedCell :=
      formalCheck { kind := .enumeration } .empty) :
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
    else checkedNumber .empty

private def repeatableDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def repeatableCheckedRead (root : CheckedCell)
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
  else
    malformedCheckedCell

private def cells3 (first second third : CheckedCell) : RowIndex → CheckedCell
  | 1 => first
  | 2 => second
  | 3 => third
  | _ => checkedNumber .empty

private def repeatableContext (root : CheckedCell)
    (rows : RowIndex → CheckedCell) : NumericComputationEvaluationContext :=
  { scalar := context root
    document := repeatableDocument [1, 2, 3]
    outer := []
    filterRead := repeatableCheckedRead root rows
    starRead := repeatableCheckedRead root rows }

private def instant : Instant := { epochMillis := 1719292867000 }

private def dateParts : DateParts := { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def dateTimeValue : Value :=
  .temporal (.dateTime instant dateParts clock .storedGregorian)

private def dateValue (year : Int) (month day : Nat)
    (basis : DateCalendarBasis := .storedGregorian) : Value :=
  .temporal (.date instant { year, month, day } basis)

private def checkedResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

private def checkedFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) : Option NumericComputationFault :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate input with
      | .ok _ => none
      | .error fault => some fault

private def targetPolicy : NumericTargetPolicy where
  info := numberInfo
  minFractionalDigits := 0
  minLeMax := by decide

private def checkedTargetResultOf
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

private def checkedDeclaredTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult :=
  match elaborateNumericTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

private def checkedBoundedScaleTwoTargetResultOf
    (value : Rat) : Option NumericTargetCheckResult :=
  match elaborateNumericTargetComputationOperation
      boundedScaleTwoModel ["Root"] boundedScaleTwoTargetId
      (.literal { value, authoredScale := 2 }) with
  | .error _ => none
  | .ok checked => checked.evaluate context |>.toOption

private def checkedRepeatableResultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationResult :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

private def checkedRepeatableFaultOf
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

private def checkedRepeatableScalarFaultOf
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

private def checkedRepeatableTargetResultOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (input : NumericComputationEvaluationContext) :
    Option NumericTargetCheckResult :=
  match elaborateNumberEntityTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

private def checkedRepeatableErrorOf
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource)) :
    Option NumericComputationElabError :=
  match elaborateNumberEntityComputationOperation
      model ["Root"] targetId expression with
  | .ok _ => none
  | .error error => some error

private def checkedProductResultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : NumericComputationEvaluationContext) :
    Option NumericComputationResult :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

private def checkedProductFaultOf
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

private def checkedProductScalarFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option NumericComputationFault :=
  match elaborateCompleteNumericComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate context with
      | .ok _ => none
      | .error fault => some fault

private def checkedProductTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (input : NumericComputationEvaluationContext) :
    Option NumericTargetCheckResult :=
  match elaborateCompleteNumericTargetComputationOperation
      model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluateIn input |>.toOption

private def targetPolicyAttachErrorOf (policy : NumericTargetPolicy) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] targetId
      (.literal { value := 0, authoredScale := 0 }) with
  | .error error => some error
  | .ok checked =>
      match checked.attachTargetPolicy policy with
      | .error error => some error
      | .ok _ => none

/- `FieldValueAsNumber` uses the checked stored/category projection in computation, preserves exact values, and maps clean absence to zero. -/
example :
    checkedResultOf (surfaceFieldValueAsNumber)
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "2")))) = some (.value 2) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.category
          (surfacePath ["Root"] "NumericChoice") "Factor"))
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 5) ∧
      checkedResultOf (surfaceFieldValueAsNumber) = some (.value 0) ∧
      checkedResultOf (surfaceFieldValueAsNumber)
        (context (choice := formalCheck { kind := .enumeration }
          (.rejected .declaredConstraint))) = some (.poison .declaredConstraint) := by
  native_decide

/- `SumOfProducts` is another ordinary numeric atom after its distinct row-aligned source has been checked: the shared expression stages the pair fold before surrounding arithmetic. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 1)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let negativeRows := cells3
      (checkedNumber (.parsed (.num (-1))))
      (checkedNumber (.parsed (.num (-3))))
      (checkedNumber (.parsed (.num (-5))))
    let input := repeatableContext (checkedNumber .empty) rows
    checkedProductResultOf
        (.binary .add surfaceProductAggregate
          (.literal { value := 1, authoredScale := 0 }))
        input =
        some (.value 45) ∧
      checkedProductTargetResultOf
        (.binary .add surfaceProductAggregate
          (.literal { value := 1, authoredScale := 0 }))
        input =
        some (.supported (.accepted { unscaled := 45, scale := 0 })) ∧
      checkedProductResultOf (.abs surfaceProductAggregate)
        (repeatableContext (checkedNumber .empty) negativeRows) =
        some (.value 44) := by
  native_decide

/- The product atom cannot cross the scalar compatibility boundary, and malformed common-row topology remains an explicit addressing fault. -/
example :
    let malformedDocument : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    let input := {
      repeatableContext (checkedNumber .empty)
        (fun _ => checkedNumber .empty) with
      document := malformedDocument }
    checkedProductScalarFaultOf surfaceProductAggregate =
        some .repeatableContextRequired ∧
      checkedProductFaultOf surfaceProductAggregate input =
        some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) := by
  native_decide

/- String and non-ASCII host-decimal sources enter the same checked computation atom and preserve exact pattern poison. -/
example :
    checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode")))
        (context (numericCode := numericString.checkRaw
          (.parsed (.str "123")))) = some (.value 123) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode")))
        (context (numericCode := numericString.checkRaw
          (.parsed (.str "12A")))) = some (.poison .declaredConstraint) ∧
      checkedResultOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "HostDigitChoice")))
        (context (hostDigitChoice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-３")))) = some (.value (-3)) := by
  native_decide

/- The converted atom composes through shared arithmetic and target checking without a conversion-specific write path. -/
example :
    let input := context (checkedNumber (.parsed (.num 3)))
      (choice := formalCheck { kind := .enumeration } (.parsed (.enum "2")))
    checkedResultOf
        (.binary .add (surfaceFieldValueAsNumber)
          (surfaceField ["Root"] "Source")) input = some (.value 5) ∧
      checkedTargetResultOf (surfaceFieldValueAsNumber) false targetPolicy input =
        some (.supported (.accepted { unscaled := 2, scale := 0 })) := by
  native_decide

/- The checked operation-form wrappers consume the converted source through the shared numeric evaluator. Rounding uses the selected category token; absolute value and both wrappers preserve clean zero or exact poison. -/
example :
    let rounded := .round .halfUp omittedRoundingPlaces
      (surfaceFieldValueAsNumber (.category
        (surfacePath ["Root"] "NumericChoice") "Fraction"))
    let absolute := .abs surfaceFieldValueAsNumber
    checkedResultOf rounded
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 1) ∧
      checkedResultOf absolute
        (context (choice := formalCheck { kind := .enumeration }
          (.parsed (.enum "-150")))) = some (.value 150) ∧
      checkedResultOf rounded = some (.value 0) ∧
      checkedResultOf absolute = some (.value 0) ∧
      checkedResultOf absolute
        (context (choice := formalCheck { kind := .enumeration }
          (.rejected .declaredConstraint))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Conversion diagnostics preserve resolved source identity and exact category rejection. -/
example :
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "Missing"))) =
      some (.resolve (.invalidEntity (surfacePath ["Root"] "Missing"))) ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "Wrong"))) =
      some (.fieldValueAsNumberNotConvertible ["Root", "Wrong"]) ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.direct
          (surfacePath ["Root"] "NumericCode"))) = none ∧
    checkedErrorOf
        (surfaceFieldValueAsNumber (.category
          (surfacePath ["Root"] "NumericChoice") "Missing")) =
      some (.fieldValueAsNumberEnumeration ["Root", "NumericChoice"]
        (.unknownCategory "Missing")) := by
  native_decide

/- Numeric computation consumes the same digits-only normalized range and maps every clean fallback to zero. -/
example :
    checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "12X")))) = some (.value 12) ∧
      checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "AB3")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "A")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 2) = some (.value 0) := by
  native_decide

/- Normalization precedes selection, and a malformed source preserves computation poison. -/
example :
    checkedResultOf (surfaceStringRange 3 3)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "1\r\n2")))) = some (.value 2) ∧
      checkedResultOf (surfaceStringRange 2 2)
        (context (code := formalCheck { kind := .string }
          (.parsed (.str "A😀B")))) = some (.value 0) ∧
      checkedResultOf (surfaceStringRange 1 1)
        (context (code := formalCheck { kind := .string }
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Direct rounding and absolute value reuse the range source and ordinary numeric wrapper evaluator, including clean missing zero and exact poison. -/
example :
    let rounded := .round .halfUp omittedRoundingPlaces (surfaceStringRange 1 2)
    let absolute := .abs (surfaceStringRange 1 2)
    let filled := context (code := formalCheck { kind := .string }
      (.parsed (.str "12X")))
    let malformed := context (code := formalCheck { kind := .string }
      (.rejected .malformed))
    checkedResultOf rounded filled = some (.value 12) ∧
      checkedResultOf absolute filled = some (.value 12) ∧
      checkedResultOf rounded = some (.value 0) ∧
      checkedResultOf absolute = some (.value 0) ∧
      checkedResultOf rounded malformed = some (.poison .malformed) ∧
      checkedResultOf absolute malformed = some (.poison .malformed) := by
  native_decide

/- The checked atom is an ordinary numeric-expression source and reaches the existing target checker without a range-specific write path. -/
example :
    let input := context
      (checkedNumber (.parsed (.num 3)))
      (code := formalCheck { kind := .string } (.parsed (.str "12X")))
    checkedResultOf
        (.binary .add (surfaceStringRange 1 2)
          (surfaceField ["Root"] "Source")) input = some (.value 15) ∧
      checkedTargetResultOf (surfaceStringRange 1 2) false targetPolicy input =
        some (.supported (.accepted { unscaled := 12, scale := 0 })) := by
  native_decide

/- Static range diagnostics preserve field-shape → interval → String-kind precedence. -/
example :
    checkedErrorOf
        (.atom (.stringRange (surfacePath ["Root"] "Missing") 0 2)) =
      some (.resolve (.invalidEntity (surfacePath ["Root"] "Missing"))) ∧
    checkedErrorOf (.atom (.stringRange (surfacePath ["Root"] "Source") 0 2)) =
      some (.invalidStringRange 0 2) ∧
    checkedErrorOf (.atom (.stringRange (surfacePath ["Root"] "Source") 1 2)) =
      some (.rangeOperandNotString ["Root", "Source"]) := by
  native_decide

private def literal (value : Rat) (authoredScale : Int := 0) :
    AuthoredNumericExpr FlatFieldDecl :=
  .literal { value, authoredScale }

private def field (declaration : FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .atom declaration

private def divide (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary .divide left right

private def binary (op : NumericScaleBinaryOp)
    (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary op left right

private def rounded (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .round .halfUp omittedRoundingPlaces body

private def absolute (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .abs body

private def power (base exponent : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .power base exponent

private def resultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  (expression.evaluateComputation input).toOption

private def faultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationFault :=
  match expression.evaluateComputation input with
  | .ok _ => none
  | .error fault => some fault

/- Checked computation-operation authoring resolves the shared numeric tree and rejects a nested direct reference to its own target. -/
example :
    checkedErrorOf
      (.binary .add (surfaceField ["Root"] "Source")
        (.group (.binary .multiply
          (surfaceField ["Root"] "Target")
          (.literal { value := 2, authoredScale := 0 })))) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf (.abs (surfaceField ["Root"] "Target")) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add (surfaceField ["Root"] "Target")
            (.literal { value := 1, authoredScale := 0 }))) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf
        (.binary .multiply
          (.round .halfUp omittedRoundingPlaces
            (surfaceField ["Root"] "Target"))
          (.literal { value := 2, authoredScale := 0 })) =
        some (.targetSelfReference targetId) := by
  native_decide

/- Target policy is attached once: a different scale/signedness summary is rejected before evaluation. -/
example :
    let wrongPolicy : NumericTargetPolicy :=
      { info := { scale := 1, signed := true }
        minFractionalDigits := 0
        minLeMax := by decide }
    targetPolicyAttachErrorOf wrongPolicy =
      some (.targetPolicyMismatch numberInfo wrongPolicy.info) := by
  native_decide

/- Evaluation consumes the retained complete policy rather than accepting a new caller-selected one. -/
example :
    let zeroForbidden := { targetPolicy with zeroAllowed := false }
    checkedTargetResultOf (.literal { value := 0, authoredScale := 0 })
      false zeroForbidden =
        some (.supported (.rejected
          { unscaled := 0, scale := 0 } .zeroNotAllowed)) := by
  native_decide

/- The ordinary checked target route constructs and retains the target policy from the validated declaration; no caller policy argument can override the zero constraint. -/
example :
    checkedDeclaredTargetResultOf
        (.literal { value := 0, authoredScale := 0 }) =
      some (.supported (.rejected
        { unscaled := 0, scale := 0 } .zeroNotAllowed)) ∧
    checkedDeclaredTargetResultOf
        (.literal { value := 3, authoredScale := 0 }) =
      some (.supported (.accepted { unscaled := 3, scale := 0 })) := by
  native_decide

/- A second declaration-owned constraint class is integrated through the same construction: minimum scale controls stored identity and the inclusive maximum remains the later target check. -/
example :
    checkedBoundedScaleTwoTargetResultOf 5 =
        some (.supported (.accepted { unscaled := 500, scale := 2 })) ∧
      checkedBoundedScaleTwoTargetResultOf 6 =
        some (.supported (.rejected
          { unscaled := 600, scale := 2 } .aboveMaximum)) := by
  native_decide

/- Number target constraints cannot be attached to another kind. -/
example :
    let nonNumber := { wrong with
      numericTargetConstraints := { zeroAllowed := false } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == wrongId then nonNumber else declaration }).validate =
      some (.numericTargetConstraintsRequireNumber nonNumber.path) := by
  native_decide

/- Required fractional digits cannot exceed the existing Number scale. -/
example :
    let excessiveMinimum := { target with
      numericTargetConstraints := { minFractionalDigits := 1 } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then excessiveMinimum else declaration }).validate =
      some (.numericMinimumFractionalDigitsExceedMaximum
        excessiveMinimum.path 1 0) := by
  native_decide

/- A present effective integer-digit capacity is positive. -/
example :
    let zeroCapacity := { target with
      numericTargetConstraints := { maxIntegerDigits := some 0 } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then zeroCapacity else declaration }).validate =
      some (.numericMaximumIntegerDigitsZero zeroCapacity.path) := by
  native_decide

/- The one legal warning suppression bypasses only the result-scale gate and selects the no-fit target branch carried by the checked operation. -/
example :
    let scaleOne :=
      AuthoredNumericExpr.literal
        (Atom := SurfaceNumericAtom) { value := 11 / 10, authoredScale := 1 }
    checkedErrorOf scaleOne =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) ∧
      checkedErrorOf scaleOne (suppressExactScaleWarning := true) = none ∧
      checkedTargetResultOf scaleOne true =
        some (.supported (.rejected
          { unscaled := 11, scale := 1 } .suppressedScaleMismatch)) := by
  native_decide

/- Suppression does not bypass the independent plain-authoring rejection. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions (suppressExactScaleWarning := true) =
      some (.authoring .tooManyDivisions) := by
  native_decide

/- A checked operation reuses the existing numeric evaluator; unlike a validation comparison, a constant-only computation is legal. -/
example :
    checkedResultOf
        (.binary .add (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (context (checkedNumber (.parsed (.num 3)))) = some (.value 5) ∧
      checkedResultOf (.literal { value := 7, authoredScale := 0 }) =
        some (.value 7) := by
  native_decide

example :
    noBaseYearErrorOf surfaceBaseYear = some .baseYearNotDeclared ∧
    checkedResultOf surfaceBaseYear = some (.value 2020) ∧
    checkedResultOf (.binary .add surfaceBaseYear
      (surfaceField ["Root"] "Source"))
      (context (checkedNumber (.parsed (.num 1)))) = some (.value 2021) ∧
    checkedErrorOf (.binary .add surfaceBaseYear
      (.literal { value := 0, authoredScale := 2 })) =
        some (.operationScaleMismatch 0
          ((NumericScaleSummary.field 0).union
            (NumericScaleSummary.constant 2))) := by
  native_decide

example :
    let directYear := surfaceBaseYearDatePart .direct .year
    let finishDay := surfaceBaseYearDatePart (.range .finish) .day
    let finishQuarter := surfaceBaseYearDatePart (.range .finish) .quarter
    noBaseYearErrorOf finishDay = some .baseYearNotDeclared ∧
      checkedResultOf directYear = some (.value 2020) ∧
      checkedResultOf finishDay = some (.value 31) ∧
      checkedResultOf finishQuarter = some (.value 4) ∧
      checkedResultOf (.abs finishDay) = some (.value 31) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces finishDay) =
        some (.value 31) ∧
      checkedResultOf (.binary .add finishDay
        (surfaceField ["Root"] "Source"))
        (context (checkedNumber (.parsed (.num 1)))) = some (.value 32) ∧
      checkedResultOf (.abs surfaceBaseYear) = some (.value 2020) ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces (.group surfaceBaseYear)) =
          some (.value 2020) := by
  native_decide

/- Direct functions are the smallest specialization of the complete numeric-operation route shared with numeric validation. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    let input := context (checkedNumber (.parsed (.num (5 / 2))))
    checkedResultOf (.round .halfUp omittedRoundingPlaces sourceField) input =
        some (.value 3) ∧
      checkedResultOf (.abs sourceField)
        (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) ∧
      checkedResultOf
        (AuthoredNumericExpr.extremumList .maximum sourceField
          [.literal { value := 4, authoredScale := 0 }]) input =
        some (.value 4) := by
  native_decide

/- Checked computation retains each operand-list call boundary while admitting complete numeric operands and surrounding arithmetic. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    let input := context (checkedNumber (.parsed (.num 5)))
    checkedResultOf
        (AuthoredNumericExpr.extremumList .minimum
          (AuthoredNumericExpr.extremumList .maximum sourceField
            [.literal { value := 1, authoredScale := 0 }])
          [.literal { value := 2, authoredScale := 0 }]) input =
        some (.value 2) ∧
      checkedResultOf
        (AuthoredNumericExpr.extremumList .minimum
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 }))
          [.group (.literal { value := 2, authoredScale := 0 })]) input =
        some (.value 2) ∧
      checkedResultOf
        (.binary .add
          (AuthoredNumericExpr.extremumList .minimum sourceField
            [.literal { value := 2, authoredScale := 0 }])
          (.literal { value := 1, authoredScale := 0 })) input =
        some (.value 3) := by
  native_decide

/- Each checked Min/Max call still rejects a second immediate constant, while unary wrappers compose in authored order around the completed call. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    checkedErrorOf
        (AuthoredNumericExpr.extremumList .minimum sourceField
          [.literal { value := 1, authoredScale := 0 },
            .literal { value := 2, authoredScale := 0 }]) =
          some .unsupportedExpression ∧
      checkedErrorOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 }))) =
          none ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 })))
        (context (checkedNumber (.parsed (.num 2)))) = some (.value 3) ∧
      checkedResultOf
        (.abs (.binary .subtract sourceField
          (surfaceField ["Root"] "Later")))
        (context (checkedNumber (.parsed (.num 2)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 3) ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .divide sourceField
            (.literal { value := 0, authoredScale := 0 }))) =
          some .domainFailure ∧
      checkedResultOf
        (.binary .add
          (.round .halfUp omittedRoundingPlaces
            (.binary .divide sourceField
              (.literal { value := 0, authoredScale := 0 })))
          (.literal { value := 1, authoredScale := 0 })) =
          some .domainFailure ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces (.abs sourceField))
        (context (checkedNumber (.parsed (.num ((-14 : Rat) / 10))))) =
          some (.value 1) ∧
      checkedResultOf
        (.abs (.round .floor omittedRoundingPlaces sourceField))
        (context (checkedNumber (.parsed (.num ((-14 : Rat) / 10))))) =
          some (.value 2) ∧
      checkedResultOf
        (.abs (AuthoredNumericExpr.extremumList .minimum sourceField
          [surfaceField ["Root"] "Later"]))
        (context (checkedNumber (.parsed (.num (-3))))
          (checkedNumber (.parsed (.num 2)))) = some (.value 3) := by
  native_decide

example :
    checkedErrorOf (surfaceField ["Root"] "Wrong") =
        some (.operandNotNumber wrong.path) ∧
      checkedErrorOf (surfaceField ["Root", "Rows"] "Repeated") =
        some (.resolve (.repeatableReference repeated.path)) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 0 }) wrongId =
        some (.targetNotNumber wrongId) := by
  native_decide

/- Authoring and result-scale checks precede runtime evaluation and retain their distinct rejection classes. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions = some (.authoring .tooManyDivisions) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 1 }) =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) := by
  native_decide

/- Empty Number is a real computation value, not clean no-selection. -/
example : resultOf (field source) = some (.value 0) := by
  rfl

example : resultOf (binary .add (field source) (literal 2)) =
    some (.value 2) := by
  native_decide

example : resultOf (field source)
    (context ((checkedNumber .empty).withFinding .required)) =
      some (.value 0) := by
  rfl

/- Checked computation shares the temporal component source seam and admits both direct operation-form wrappers. -/
example :
    checkedResultOf (surfaceDateFieldPart "DateTime" .day)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 25) ∧
      checkedResultOf (.abs (surfaceDateFieldPart "DateTime" .day))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 25) ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces
          (surfaceTimeFieldPart "DateTime" .second))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 7) ∧
      checkedResultOf (surfaceTimeFieldPart "DateTime" .second)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 7) ∧
      checkedResultOf (surfaceTimeFieldPart "Time" .hour) = some (.value 0) ∧
      checkedResultOf (.abs (surfaceTimeFieldPart "Time" .hour)) =
        some (.value 0) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces
        (surfaceDateFieldPart "DateTime" .year))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Checked computation consumes the same mixed date-difference source: filled fields produce scale-0 values, empty is zero, and formal invalidity remains poison. -/
example :
    let mixedMonths := surfaceDateDifference .months
      (.baseYear .direct) (surfaceDateOperand "Date")
    let reverseMonths := surfaceDateDifference .months
      (surfaceDateOperand "Date") (.baseYear .direct)
    checkedResultOf mixedMonths (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf (.abs reverseMonths) (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces mixedMonths) (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf mixedMonths = some (.value 0) ∧
      checkedResultOf (.abs mixedMonths) = some (.value 0) ∧
      checkedResultOf (.abs mixedMonths)
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Month/year differences reject DateTime statically and a legacy-hybrid field payload dynamically instead of applying the proleptic decoded-parts core. -/
example :
    checkedErrorOf (surfaceDateDifference .years
      (surfaceDateOperand "DateTime") (.baseYear .direct)) =
        some (.incompatibleTemporalSource ["Root", "DateTime"]) ∧
      checkedFaultOf
        (surfaceDateDifference .months
          (.baseYear .direct) (surfaceDateOperand "Date"))
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29 .legacyHybrid)))) =
          some .unsupportedDateCalendar := by
  native_decide

/- Checked source admission rejects the wrong temporal family while admitting numeric `BaseYear` under the ordinary wrappers. -/
example :
    checkedErrorOf (surfaceDateFieldPart "Time" .day) =
        some (.incompatibleTemporalSource ["Root", "Time"]) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces surfaceBaseYear) =
        some (.value 2020) := by
  native_decide

example : resultOf (divide (literal 6) (literal 3)) = some (.value 2) := by
  native_decide

/- The computation consumer uses the established one-pass lowering rather than folding the authored tree directly. -/
example : resultOf
    (binary .multiply (literal 3)
      (.group (divide (literal 1) (literal 3)))) =
      some (.value 1) := by
  native_decide

/- Arithmetic domain failure survives as its own expression outcome. -/
example : resultOf (divide (literal 1) (literal 0)) = some .domainFailure := by
  native_decide

/- Rounding does not turn a failed arithmetic child into a numeric value. -/
example : resultOf (rounded (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

/- Rounding preserves a reached computation poison instead of manufacturing a numeric result. -/
example : resultOf (rounded (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- Absolute value shares the numeric tree but preserves computation-domain failure and poison. -/
example : resultOf (absolute (field source))
    (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) := by
  native_decide

example : resultOf (absolute (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

example : resultOf (absolute (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- Numeric operand-list extrema keep empty Number as a competing zero. -/
example : resultOf (AuthoredNumericExpr.extremumList .minimum (field source) [literal 4]) =
    some (.value 0) := by
  native_decide

example : resultOf (AuthoredNumericExpr.extremumList .maximum (field source) [literal (-4)]) =
    some (.value 0) := by
  native_decide

/- A domain failure remains value-level and therefore does not hide a later reached poison. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum
      (divide (literal 1) (literal 0)) [literal 3]) =
      some .domainFailure := by
  native_decide

example : resultOf
    (AuthoredNumericExpr.extremumList .minimum
      (divide (literal 1) (literal 0)) [literal 3, field later])
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  native_decide

/- The first poison aborts the remaining ordered operand stream. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum (field source) [field later])
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  native_decide

/- Structural preflight traverses the complete list before a reached poison could hide a wrong-kind tail. -/
example : faultOf
    (AuthoredNumericExpr.extremumList .minimum (field source)
      [literal 3, field (stringDeclaration laterId "WrongLater")])
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

example : resultOf
    (binary .add (divide (literal 1) (literal 0)) (literal 2)) =
      some .domainFailure := by
  native_decide

example : resultOf
    (binary .add (literal 2) (divide (literal 1) (literal 0))) =
      some .domainFailure := by
  native_decide

/- A formally invalid field actually read by the expression remains poison. -/
example : resultOf (field source)
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- The source-generated arithmetic chain still evaluates its right operand after a domain-invalid receiver; a reached invalid field therefore remains poison. Portable mixed-precedence evidence remains pending. -/
example : resultOf
    (binary .add
      (divide (literal 1) (literal 0))
      (field later))
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A left poison aborts before a differently poisoned right operand can replace its cause. -/
example : resultOf
    (binary .add
      (field source)
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  rfl

/- Poison order follows the one-pass lowered tree: `(Source / 2) * Later` becomes `(Later * Source) / 2`, so Later is read first. -/
example : resultOf
    (binary .multiply
      (divide (field source) (literal 2))
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A non-Number declaration is a structural fault even when its cell is empty. -/
example : faultOf (field (stringDeclaration sourceId "WrongSource")) =
      some (.fieldKindMismatch sourceId) := by
  native_decide

/- Complete structural checking prevents a left poison from hiding a wrong-kind right declaration. -/
example : faultOf
    (binary .add
      (field source)
      (field (stringDeclaration laterId "WrongLater")))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

/- Power shares the checked computation result boundary: valid values remain values. -/
example : resultOf (power (literal 2) (literal 3)) =
    some (.value 8) := by
  native_decide

/- Both runtime-invalid integral power regions become arithmetic domain failure. -/
example : resultOf (power (literal 0) (literal (-1))) =
    some .domainFailure := by
  native_decide

example : resultOf (power (literal 2) (literal 1001)) =
    some .domainFailure := by
  native_decide

/- Structural preflight still traverses power before a reached poison can hide a wrong-kind exponent. -/
example : faultOf
    (binary .add (field source)
      (power (literal 2) (field (stringDeclaration laterId "WrongLater"))))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

/- Computation consumes the same resolved aggregate source and fold: empties are skipped, all-empty is zero, and reached formal invalidity poisons. -/
example :
    checkedResultOf (surfaceAggregate .sum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) ∧
      checkedResultOf (surfaceAggregate .sum "Source" ["Later"]) =
        some (.value 0) ∧
      checkedResultOf (surfaceAggregate .minimum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))) = some (.value 20) ∧
      checkedResultOf (surfaceAggregate .maximum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))
          (checkedNumber (.rejected .declaredConstraint))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- A filtered repeatable aggregate is one ordinary numeric atom: it composes with arithmetic and reaches the existing target checker without a top-level special path. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let input := repeatableContext
      (checkedNumber (.parsed (.num 3))) rows
    let expression :=
      AuthoredNumericExpr.binary .add
        (surfaceRepeatableAggregate .sum)
        (.literal { value := 1, authoredScale := 0 })
    checkedRepeatableResultOf expression input = some (.value 7) ∧
      checkedRepeatableTargetResultOf expression input =
        some (.supported (.accepted { unscaled := 7, scale := 0 })) := by
  native_decide

/- A repeatable aggregate never degrades into a scalar empty-document result, and malformed row topology stays an explicit addressing fault. -/
example :
    let rows := cells3
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 3)))
      (checkedNumber (.parsed (.num 5)))
    let input := repeatableContext
      (checkedNumber (.parsed (.num 3))) rows
    let malformedDocument : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    checkedRepeatableScalarFaultOf
        (surfaceRepeatableAggregate .sum) =
      some .repeatableContextRequired ∧
    checkedRepeatableFaultOf
        (surfaceRepeatableAggregate .sum)
        { input with document := malformedDocument } =
      some (.repeatableAddressing (.invalidRowDepth 10 [1, 2] 1)) := by
  native_decide

/- Computation target self-reference traverses both the entity-list targets and the `Having` filter tree. -/
example :
    let directTarget :
        AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
      .atom (.aggregate .sum {
        first := .field (surfacePath ["Root"] "Target")
        rest := [.star repeatedStarPath] })
    checkedRepeatableErrorOf directTarget =
        some (.targetSelfReference targetId) ∧
      checkedRepeatableErrorOf
        (surfaceRepeatableAggregate .sum "Target") =
        some (.targetSelfReference targetId) := by
  native_decide

/- NumberOfDifferentValues uses the same checked computation atom, drops empty cells, and preserves formal poison while exposing only the integral value. -/
example :
    checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 5)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber .empty)
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf (surfaceAggregate .distinctCount "Source" ["Later"])
        (context (checkedNumber (.rejected .declaredConstraint))
          (checkedNumber (.parsed (.num 5)))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Aggregate atoms compose through plain arithmetic and the kernel-established direct rounding route while retaining their derived scale. -/
example :
    checkedResultOf
      (.binary .add (surfaceAggregate .sum "Source" ["Later"])
        (.literal { value := 1, authoredScale := 0 }))
      (context (checkedNumber (.parsed (.num 4)))
        (checkedNumber (.parsed (.num 6)))) = some (.value 11) ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (surfaceAggregate .sum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) := by
  native_decide

/- Fixed group counts remain validation-only until checked computation scheduling owns group-state dependencies and clearing. -/
example : checkedErrorOf surfaceFixedGroupCount = some .unsupportedExpression := by
  native_decide

/- Direct aggregate `Abs` runs after the shared fold, including negative totals, all-empty zero, and exact poison. A wrapper may also consume a checked operand-list extremum. -/
example :
    let aggregate := surfaceAggregate .sum "Source" ["Later"]
    checkedResultOf (.abs aggregate)
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 6) ∧
      checkedResultOf (.abs aggregate) = some (.value 0) ∧
      checkedResultOf (.abs aggregate)
        (context (checkedNumber (.rejected .declaredConstraint))) =
          some (.poison .declaredConstraint) ∧
      checkedResultOf
        (.abs (surfaceAggregate .minimum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 10) ∧
      checkedResultOf
        (.abs (surfaceAggregate .maximum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 4) ∧
      checkedResultOf
        (.abs (surfaceAggregate .distinctCount "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num 5)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 1) ∧
      checkedResultOf
        (.abs (AuthoredNumericExpr.extremumList .minimum aggregate
          [surfaceField ["Root"] "Source"]))
        (context (checkedNumber (.parsed (.num (-10))))
          (checkedNumber (.parsed (.num 4)))) = some (.value 10) := by
  native_decide

/- Shared aggregate lowering preserves its diagnostic owner and computation's nested target-reference rejection. -/
example :
    checkedErrorOf (surfaceAggregate .sum "Source" ["Wrong"]) =
        some (.aggregate (.fieldKindMismatch ["Root", "Wrong"] .string)) ∧
      checkedErrorOf (surfaceAggregate .sum "Source" ["Target"]) =
        some (.targetSelfReference targetId) := by
  native_decide

end A12Kernel.Conformance.NumericComputation
