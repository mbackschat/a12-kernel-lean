import A12Kernel.Conformance.Elaboration.Support

/-! # Flat model, path, and condition elaboration locks -/

namespace A12Kernel.Conformance.Elaboration.Static

open A12Kernel
open A12Kernel.Conformance.Elaboration.Support

/- The checked flat certificate retains the exact declaring group needed for later mixed-condition composition. -/
example : rowGroupOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) = some ["Order"] := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.compare (.boolean .equal { id := 1 } false)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .notEqual (absolute ["Order"] "TermsConfirmed") (.boolean true))) =
    some (.compare (.confirm .notEqual { id := 2 })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldNotFilled (absolute ["Order"] "Quantity"))) =
    some (.fieldNotFilled (.number { id := 0, info := numberInfo })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order"] "Note"))) =
    some (.fieldFilled (.string { id := 7 })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order"] "DispatchDate"))) =
    some (.fieldFilled (.temporal
      { id := 8, kind := .date, components := dispatchDateComponents })) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compareFields .less "DispatchDate" "ArrivalDate")) =
    some (.compare (.temporal .before
      (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
      (.fieldValue { id := 9, kind := .date, components := dispatchDateComponents }))) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareFields .less "DispatchDate" "EventDateTime")) =
        some (.compare (.temporal .before
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) ∧
      errorOf (elaborate model ["Order"]
        (compareFields .equal "DispatchDate" "EventDateTime")) =
          some (.temporalFormatsIncompatible
            ["Order", "DispatchDate"] ["Order", "EventDateTime"]) := by
  native_decide

/-! The core admits field/literal in either operand position for later expression lowering, but never the kernel-forbidden constant/constant comparison. -/
example : model.admitsComparison
    (.temporal .equal
      (.literalValue { epochMillis := 100000 })
      (.literalValue { epochMillis := 100000 })) = false := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compare .less (absolute ["Order"] "DispatchDate")
        (dateLiteral dispatchDateComponents 101000))) =
      some (.compare (.temporal .before
        (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
        (.literalValue { epochMillis := 101000 }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compare .equal (absolute ["Order"] "EventDateTime")
        (dateLiteral dispatchDateComponents 101000))) =
        some (.temporalFormatsIncompatible
          ["Order", "EventDateTime"] ["<date-literal>"]) ∧
      (elaborate model ["Order"]
        (compare .less (absolute ["Order"] "EventDateTime")
          (dateLiteral dispatchDateComponents 101000))).isOk = true := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compare .less (absolute ["Order"] "RecurringDate")
        (dateLiteral monthDayComponents 101000))) =
        some (.temporalLiteralNeedsBaseYear ["<date-literal>"]) ∧
      (elaborate baseYearModel ["Order"]
        (compare .less (absolute ["Order"] "RecurringDate")
          (dateLiteral monthDayComponents 101000))).isOk = true := by
  native_decide

private def invalidDateLiteralComponents : TemporalComponents :=
  { year := true, month := false, day := true,
    hour := false, minute := false, second := false }

example :
    errorOf (elaborate model ["Order"]
      (compare .equal (absolute ["Order"] "DispatchDate")
        (dateLiteral invalidDateLiteralComponents 101000))) =
      some (.invalidTemporalLiteralComponents ["<date-literal>"]) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareNow .less .right "EventDateTime")) =
        some (.compare (.temporal .before
          (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents })
          .nowValue)) ∧
      coreOf (elaborate model ["Order"]
        (compareNow .greater .left "EventDateTime")) =
          some (.compare (.temporal .after .nowValue
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareNow .less .right "DispatchDate")) =
        some (.temporalNowRequiresTime ["Order", "DispatchDate"]) := by
  native_decide

example :
    coreOf (elaborate model ["Order"]
      (compareToday .equal .right "DispatchDate")) =
        some (.compare (.temporal .equal
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.todayValue "UTC"))) ∧
      coreOf (elaborate model ["Order"]
        (compareToday .less .left "EventDateTime")) =
          some (.compare (.temporal .before (.todayValue "UTC")
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareToday .equal .right "EventDateTime")) =
        some (.temporalFormatsIncompatible ["Order", "EventDateTime"] ["<Today>"]) ∧
      errorOf (elaborate model ["Order"]
        (compareToday .less .right "EventTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventTime"] ["<Today>"]) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareBaseYear .equal .right "DispatchDate")) =
        some .baseYearNotDeclared ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "Limit")) =
          some (.compare (.number (.ordinary .equal)
            { id := 3, info := { scale := 0, signed := true } } 2020)) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "Quantity")) =
          some (.baseYearScaleMismatch ["Order", "Quantity"] 2) := by
  native_decide

example :
    coreOf (elaborate baseYearModel ["Order"]
      (compareBaseYear .equal .right "DispatchDate")) =
        some (.compare (.temporal .equal
          (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
          (.baseYearValue "UTC" 2020))) ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .less .left "EventDateTime")) =
          some (.compare (.temporal .before (.baseYearValue "UTC" 2020)
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .equal .right "EventDateTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventDateTime"] ["<BaseYear>"]) ∧
      errorOf (elaborate baseYearModel ["Order"]
        (compareBaseYear .less .right "EventTime")) =
          some (.temporalFormatsIncompatible ["Order", "EventTime"] ["<BaseYear>"]) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareBaseYearRange .equal .right .start "DispatchDate")) =
        some .baseYearNotDeclared ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYearRange .equal .right .start "DispatchDate")) =
          some (.compare (.temporal .equal
            (.fieldValue { id := 8, kind := .date, components := dispatchDateComponents })
            (.baseYearRangeValue "UTC" 2020 .start))) ∧
      coreOf (elaborate baseYearModel ["Order"]
        (compareBaseYearRange .less .left .finish "EventDateTime")) =
          some (.compare (.temporal .before
            (.baseYearRangeValue "UTC" 2020 .finish)
            (.fieldValue { id := 11, kind := .dateTime, components := dateTimeComponents }))) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .equal .right .finish "EventDateTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "EventDateTime"] ["<EndOfDateRange(BaseYear)>"]) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .less .right .start "EventTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "EventTime"] ["<StartOfDateRange(BaseYear)>"]) := by
  native_decide

/- Base Year can supply a missing year to a date fragment, but cannot turn a Time field into a date-bearing operand. -/
example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareFields .less "DispatchDate" "EventTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "DispatchDate"] ["Order", "EventTime"]) := by
  native_decide

example :
    errorOf (elaborate baseYearModel ["Order"]
      (compareBaseYearRange .equal .right .start "Limit")) =
      some (.temporalOperandKindMismatch
        ["Order", "Limit"] ["<StartOfDateRange(BaseYear)>"]
        .number (.temporal .date)) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareFields .less "DispatchDate" "EventTime")) =
        some (.temporalFormatsIncompatible
          ["Order", "DispatchDate"] ["Order", "EventTime"]) ∧
      errorOf (elaborate model ["Order"]
        (compareFields .equal "DispatchDate" "ExpressShipping")) =
          some (.temporalOperandKindMismatch
            ["Order", "DispatchDate"] ["Order", "ExpressShipping"]
            (.temporal .date) .boolean) := by
  native_decide

example :
    errorOf (elaborate model ["Order"]
      (compareFields .less "RecurringDate" "DispatchDate")) =
        some (.temporalFormatsIncompatible
          ["Order", "RecurringDate"] ["Order", "DispatchDate"]) ∧
      (elaborate baseYearModel ["Order"]
        (compareFields .less "RecurringDate" "DispatchDate")).isOk = true := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (.and (.fieldFilled (absolute ["Order"] "ExpressShipping"))
      (compare .equal (absolute ["Order"] "Quantity") (.number 0)))) =
    some (.and (FlatCondition.fieldFilled (.boolean { id := 1 }))
      (FlatCondition.compare (.number (.ordinary .equal)
        { id := 0, info := numberInfo } 0))) := by
  native_decide

-- Bare resolution is declaring-group-first, then flag-gated unique model-wide.
example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Limit")) = some 4 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "Quantity")) = some 0 := by
  native_decide

-- Ancestors have no special tier: after a local miss, duplicate names are model-wide ambiguous.
example : errorOf (model.resolveField ["Order", "Details", "Deep"] (bare "Limit")) =
    some (.shortNameNotUnique "Limit") := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"] (bare "ExternalCode")) = some 5 := by
  native_decide

example : resolvedIdOf (model.resolveField ["Order", "Details"]
    (relative 1 [] "Quantity")) = some 0 := by
  native_decide

/- An explicit turning-point name validates the group reached by the authored `..` count without changing the resolved target. -/
example :
    let namedParent : SurfaceFieldPath :=
      { base := .relative 1, turningPoint := some "Order",
        groups := [], field := "Quantity" }
    let wrongName : SurfaceFieldPath :=
      { namedParent with turningPoint := some "Details" }
    let namedAbsolute : SurfaceFieldPath :=
      { base := .absolute, turningPoint := some "Order",
        groups := ["Order"], field := "Quantity" }
    let namedWithoutParent : SurfaceFieldPath :=
      { base := .relative 0, turningPoint := some "Order",
        groups := [], field := "Quantity" }
    resolvedIdOf (model.resolveField ["Order", "Details"] namedParent) = some 0 ∧
      errorOf (model.resolveField ["Order", "Details"] wrongName) =
        some (.invalidEntity wrongName) ∧
      errorOf (model.resolveField ["Order", "Details"] namedAbsolute) =
        some (.invalidReference namedAbsolute) ∧
      errorOf (model.resolveField ["Order", "Details"] namedWithoutParent) =
        some (.invalidReference namedWithoutParent) := by
  native_decide

example : errorOf (model.resolveField ["Order", "Details"]
    (relative 2 [] "Quantity")) = some (.aboveRoot 2) := by
  native_decide

private def ambiguousModel : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["One"], name := "Code", policy := { kind := .boolean } },
      { id := 1, groupPath := ["Two"], name := "Code", policy := { kind := .boolean } }],
    fieldRefByShortNameAllowed := true }

example : errorOf (ambiguousModel.resolveField ["Rule"] (bare "Code")) =
    some (.shortNameNotUnique "Code") := by
  native_decide

private def shortNamesDisabled : FlatModel :=
  { model with fieldRefByShortNameAllowed := false }

-- The declaring-group tier does not depend on the model-wide short-name flag.
example : resolvedIdOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "Limit")) = some 4 := by
  native_decide

-- There is no implicit ancestor walk when short-name fallback is disabled.
example : errorOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "Quantity")) = some (.invalidEntity (bare "Quantity")) := by
  native_decide

example : errorOf (shortNamesDisabled.resolveField ["Order", "Details"]
    (bare "ExternalCode")) = some (.invalidEntity (bare "ExternalCode")) := by
  native_decide

example : errorOf (model.resolveField ["Order"]
    (absolute ["Order"] "Missing")) =
    some (.invalidEntity (absolute ["Order"] "Missing")) := by
  native_decide

private def keywordProfile : PathKeywordProfile :=
  { reserved := ["And", "Date", "Today"] }

private def pathName (text : String) (quoted : Bool := false) :
    AuthoredPathName :=
  { text, quoted }

private def keywordFieldModel : FlatModel :=
  { fields := [
      { id := 20, groupPath := ["Order"], name := "Date",
        policy := { kind := .string } },
      { id := 22, groupPath := ["Order"], name := "date",
        policy := { kind := .string } },
      { id := 21, groupPath := ["Order", "And"], name := "Value",
        policy := { kind := .boolean } }] }

/- A reserved field name reaches ordinary lookup only when the authored path retained its single quotes. -/
example :
    let unquoted : AuthoredFieldPath := {
      base := .absolute
      groups := [pathName "Order"]
      field := pathName "Date"
    }
    let quoted : AuthoredFieldPath := {
      unquoted with field := pathName "Date" true
    }
    errorOf (keywordFieldModel.resolveAuthoredField
      keywordProfile ["Order"] unquoted) =
        some (.syntax (.unquotedKeyword "Date")) ∧
      (valueOf (keywordFieldModel.resolveAuthoredField
        keywordProfile ["Order"] quoted)).map (·.id) = some 20 ∧
      (valueOf (keywordFieldModel.resolveAuthoredField
        keywordProfile ["Order"] {
          unquoted with field := pathName "date"
        })).map (·.id) = some 22 := by
  native_decide

/- The same quote gate applies to group names, not only the terminal field segment. -/
example :
    let unquoted : AuthoredFieldPath := {
      base := .absolute
      groups := [pathName "Order", pathName "And"]
      field := pathName "Value"
    }
    let quoted : AuthoredFieldPath := {
      unquoted with
        groups := [pathName "Order", pathName "And" true]
    }
    let unnecessarilyQuoted : AuthoredFieldPath := {
      quoted with field := pathName "Value" true
    }
    errorOf (keywordFieldModel.resolveAuthoredField
      keywordProfile ["Order"] unquoted) =
        some (.syntax (.unquotedKeyword "And")) ∧
      (valueOf (keywordFieldModel.resolveAuthoredField
        keywordProfile ["Order"] quoted)).map (·.id) = some 21 ∧
      (valueOf (keywordFieldModel.resolveAuthoredField
        keywordProfile ["Order"] unnecessarilyQuoted)).map (·.id) = some 21 := by
  native_decide

/- Canonical reification quotes only exact keyword collisions and lowers back to the same structured path. -/
example :
    let path := absolute ["Order"] "Date"
    path.reifyQuotes keywordProfile = {
      base := .absolute
      groups := [pathName "Order"]
      field := pathName "Date" true
    } ∧
      valueOf ((path.reifyQuotes keywordProfile).lower keywordProfile) =
        some path := by
  constructor <;> native_decide

private def duplicateIdModel : FlatModel :=
  { fields := [quantityDecl, { expressDecl with id := 0 }] }

example : errorOf (elaborate duplicateIdModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateFieldId 0)) := by
  native_decide

private def duplicatePathModel : FlatModel :=
  { fields := [quantityDecl, { quantityDecl with id := 9 }] }

example : errorOf (elaborate duplicatePathModel ["Order"]
    (.fieldFilled (absolute ["Order"] "Quantity"))) =
    some (.resolve (.duplicateEntityPath ["Order", "Quantity"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (.fieldFilled (absolute ["Order", "Items"] "Count"))) =
    some (.resolve (.repeatableReference ["Order", "Items", "Count"])) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "Quantity") (.boolean true))) =
    some (.literalKindMismatch ["Order", "Quantity"] .number .boolean) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .equal (absolute ["Order"] "TermsConfirmed") (.boolean false))) =
    some (.illegalConfirmLiteral ["Order", "TermsConfirmed"]) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .less)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .greaterEqual (absolute ["Order"] "Quantity") (.number 0))) =
    some (.compare (.number (.ordinary .greaterEqual)
      { id := 0, info := numberInfo } 0)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .lessEqual (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .lessEqual)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : coreOf (elaborate model ["Order"]
    (compare .greater (absolute ["Order"] "Quantity") (.number 10))) =
    some (.compare (.number (.ordinary .greater)
      { id := 0, info := numberInfo } 10)) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .lessEqual (absolute ["Order"] "Missing") (.number 10))) =
    some (.resolve (.invalidEntity (absolute ["Order"] "Missing"))) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "ExpressShipping") (.boolean false))) =
    some (.unsupportedOperator .less) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .less (absolute ["Order"] "ExpressShipping") (.number 10))) =
    some (.unsupportedOperator .less) := by
  native_decide

example : errorOf (elaborate model ["Order"]
    (compare .greaterEqual (absolute ["Order"] "TermsConfirmed") (.boolean false))) =
    some (.unsupportedOperator .greaterEqual) := by
  native_decide


end A12Kernel.Conformance.Elaboration.Static
