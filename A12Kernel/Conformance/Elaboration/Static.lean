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

/-! ## The DateTime family's cross-kind comparison, Kernel-measured

The declared format decides a temporal cell's family at admission, at the store, and at comparison,
and it now does so across **all three** date-bearing kinds with each kind on both sides of both
outcomes in every family ([inbound](../../../docs/SOURCES.md#inbound-2026-09-05d)). Neither estate's
DATE/TIME grid could give that: a comparison row read off a classifier grid's DATE_TIME declaration
would have been the scope transfer both projects spent the week catching.

These rows had landed as a *committed but unmeasured* account, on the ground that the gate is one
component-keyed function shared with the measured pair — `compareFields` reads the two component sets
and carries the kinds into the operand without consulting them. The peer's 2x2 confirms every cell on
an independently authored carrier, and both admitted arms run tri-engine, so the admission verdicts
are not standing in for runtime ones.

A **DATE_TIME** declared date-only compares with an ordinary DATE and is refused against a real
DATE_TIME; a **DATE** declared date-and-time does the exact opposite. One direction alone would read
as "DATE_TIME is permissive"; the pair rules that out. -/
example :
    (coreOf (elaborate model ["Order"]
      (compareFields .equal "StampAsDate" "DispatchDate"))).isSome = true ∧
    errorOf (elaborate model ["Order"]
        (compareFields .equal "StampAsDate" "EventDateTime")) =
      some (.temporalFormatsIncompatible
        ["Order", "StampAsDate"] ["Order", "EventDateTime"]) ∧
    (coreOf (elaborate model ["Order"]
      (compareFields .equal "DateAsStamp" "EventDateTime"))).isSome = true ∧
    errorOf (elaborate model ["Order"]
        (compareFields .equal "DateAsStamp" "DispatchDate")) =
      some (.temporalFormatsIncompatible
        ["Order", "DateAsStamp"] ["Order", "DispatchDate"]) := by
  native_decide

/- The declared kind survives into the operand and takes no part in the decision, which is the whole
   claim: the admitted cross-kind leaf carries `dateTime` beside `date` and was admitted anyway. -/
example : coreOf (elaborate model ["Order"]
    (compareFields .equal "StampAsDate" "DispatchDate")) =
    some (.compare (.temporal .equal
      (.fieldValue
        { id := 13, kind := .dateTime, components := dispatchDateComponents })
      (.fieldValue
        { id := 8, kind := .date, components := dispatchDateComponents }))) := by
  native_decide

/- And the equality/ordering split cuts across the cross-kind case, which a reader would not predict:
   the same pair equality refuses is **ordering**-comparable, because only equality requires matching
   time presence. Without this row the refusal above would read as "these two never compare".

   This row is **internal**: the inbound 2x2 measures equality only, so ordering across a cross-kind
   pair is this project's own account through the one gate rather than a measured cell. -/
example : (coreOf (elaborate model ["Order"]
    (compareFields .less "DateAsStamp" "DispatchDate"))).isSome = true := by
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

/-- Two **root** groups, which the Kernel admits: a model with more than one root is authorable and
kernel-valid, so the model-wide short-name tier has a reach these cases can separate. `Code` is
declared once in each root; `Only` is declared once in the whole model. -/
private def ambiguousModel : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["One"], name := "Code", policy := { kind := .boolean } },
      { id := 1, groupPath := ["Two"], name := "Code", policy := { kind := .boolean } },
      { id := 2, groupPath := ["Two"], name := "Only", policy := { kind := .boolean } }],
    fieldRefByShortNameAllowed := true }

example : errorOf (ambiguousModel.resolveField ["Rule"] (bare "Code")) =
    some (.shortNameNotUnique "Code") := by
  native_decide

-- The model-wide tier is model-wide, not root-wide: a unique short name resolves from another root.
example : resolvedIdOf (ambiguousModel.resolveField ["One"] (bare "Only")) = some 2 := by
  native_decide

/- The declaring-group tier wins over a **cross-root** duplicate, which is the asymmetry that keeps the
two tiers apart: the same bare name reaches its own root's declaration from inside either root, and is
ambiguous only from a group that declares neither. Scoping the model-wide tier to the rule's own root
would keep these two rows and lose the one above. -/
example :
    resolvedIdOf (ambiguousModel.resolveField ["One"] (bare "Code")) = some 0 ∧
      resolvedIdOf (ambiguousModel.resolveField ["Two"] (bare "Code")) = some 1 := by
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

/- **A failed resolution reports one Kernel class per failure, the same on every carrier measured**, so
   the class is the resolver's. The root class reads which segment missed rather than the path's depth:
   an undeclared first segment reports it whatever follows, alone, and when it names a declared group
   that is not a root, while a miss below a declared root is the entity class. A lone declared root is a
   group in a field slot, whose class each carrier chooses, so the resolver projects none
   ([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)). -/
example :
    let key? (group : GroupPath) (reference : SurfaceFieldPath) : Option KernelStaticDiagnostic :=
      match model.resolveField group reference with
      | .ok _ => none
      | .error error => error.diagnostic?
    key? ["Order"] (absolute ["Order"] "Missing") = some .invalidEntity ∧
      key? ["Order"] (absolute ["Nope"] "Quantity") = some .invalidRootGroup ∧
      key? ["Order"] (absolute ["Nope", "Details"] "Limit") = some .invalidRootGroup ∧
      key? ["Order"] (absolute ["Details"] "Limit") = some .invalidRootGroup ∧
      key? ["Order"] (absolute [] "Nope") = some .invalidRootGroup ∧
      key? ["Order"] (absolute ["Order", "Nope"] "Limit") = some .invalidEntity ∧
      key? ["Order"] (absolute [] "Order") = none ∧
      key? ["Order"] (bare "Nope") = some .invalidEntity ∧
      key? ["Order", "Details"] (relative 2 [] "Quantity") = some .tooManyParentGroups ∧
      key? ["Order"] (absolute ["Order", "Details"] "Limit") = none := by
  native_decide

/- A bare name that misses its declaring group and then matches several fields model-wide is a class
   of its own, not a miss, and one class on every carrier measured, a computation included
   ([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-short-name-ambiguity-every-carrier)). -/
example :
    (match model.resolveField ["Order", "Details", "Deep"] (bare "Limit") with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .fieldNameNotUnique := by
  native_decide

/-- `Remark` is declared in `Insured` and in `Claims`, `Age` only in `Insured`, `ClaimRef` only in
`Claims`, and `/Policy` declares neither, as in the peer's `policy` model. -/
private def policyModel (shortNames : Bool := true) : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["Policy"], name := "Holder", policy := { kind := .string } },
      { id := 1, groupPath := ["Policy", "Insured"], name := "Remark", policy := { kind := .string } },
      { id := 2, groupPath := ["Policy", "Insured"], name := "Age", policy := { kind := .string } },
      { id := 3, groupPath := ["Policy", "Claims"], name := "Remark", policy := { kind := .string } },
      { id := 4, groupPath := ["Policy", "Claims"], name := "ClaimRef", policy := { kind := .string } },
      { id := 5, groupPath := ["Policy", "Broker"], name := "BrokerName",
        policy := { kind := .string } }]
    fieldRefByShortNameAllowed := shortNames }

/- The short-name fallback answers a relative path's **first** segment whatever follows it: an
   ambiguous one is the not-unique class where a positional reading names a miss, a unique one binds
   its field so the segment below misses, and without the flag both miss. A first segment naming a
   local group takes no fallback, so a later segment never reaches it
   ([inbound](../../../docs/SOURCES.md#inbound-2026-09-24c-path-walk)). -/
example :
    let key? (m : FlatModel) (reference : SurfaceFieldPath) : Option KernelStaticDiagnostic :=
      match m.resolveField ["Policy"] reference with
      | .ok _ => none
      | .error error => error.diagnostic?
    key? (policyModel) (relative 0 ["Remark"] "Nope") = some .fieldNameNotUnique ∧
      key? (policyModel) (relative 0 ["Age"] "Nope") = some .invalidEntity ∧
      key? (policyModel false) (relative 0 ["Remark"] "Nope") = some .invalidEntity ∧
      key? (policyModel false) (relative 0 ["Age"] "Nope") = some .invalidEntity ∧
      key? (policyModel) (relative 0 ["Insured"] "Holder") = some .invalidEntity ∧
      key? (policyModel) (relative 0 ["Broker"] "Age") = some .invalidEntity ∧
      key? (policyModel) (relative 0 ["Insured"] "ClaimRef") = some .invalidEntity ∧
      resolvedIdOf ((policyModel).resolveField ["Policy"] (relative 0 ["Insured"] "Remark")) =
        some 1 := by
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
    some (.resolve (.unboundOperandLevel ["Order", "Items", "Count"]
      { level := 10, placement := .contained, parallel := false, indexKeyed := false })) := by
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


/-! ### The field-value read's gates

A bracketed field read asks the entity it names four gates once its bracket closes, after the
reader's own classes ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)).
This carrier has no Kernel projection of its own, so the locks read the resolution failure's class.
-/

private def partialDispatchDecl : FlatFieldDecl :=
  { dispatchDateDecl with
    id := 20, name := "PartialDispatch"
    temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }

private def rawNoteDecl : FlatFieldDecl :=
  { noteDecl with
    id := 21, name := "RawNote", stringValueMode := .raw
    stringPolicy := { lineBreaksPermitted := true } }

private def ledgerTotalDecl : FlatFieldDecl :=
  { quantityDecl with id := 22, groupPath := ["Order", "Ledger"], name := "Total" }

private def readModel : FlatModel :=
  { model with
    fields := model.fields ++ [partialDispatchDecl, rawNoteDecl, ledgerTotalDecl]
    baseYear := some 2020 }

private inductive ReadView where
  | admitted
  | refused (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

private def readViewIn (readModel : FlatModel) (condition : SurfaceCondition) : ReadView :=
  match elaborate readModel ["Order"] condition with
  | .ok _ => .admitted
  | .error (.resolve error) => .refused error.diagnostic?
  | .error _ => .refused none

private def readView : SurfaceCondition → ReadView := readViewIn readModel

/- **A partially known Date is refused a value read**, on either side of a comparison between two
   fields and against `Today`, where the same read of a Date of full precision is admitted. A gate
   reading only the declared components admits all three. -/
example :
    [readView (compareFields .greater "PartialDispatch" "DispatchDate"),
      readView (compareFields .equal "DispatchDate" "PartialDispatch"),
      readView (compareToday .less .right "PartialDispatch"),
      readView (compareFields .equal "DispatchDate" "DispatchDate"),
      readView (compareToday .less .right "DispatchDate")] =
      [.refused (some .invalidDateType), .refused (some .invalidDateType),
        .refused (some .invalidDateType), .admitted, .admitted] := by
  native_decide

/- **Each bracket is checked as it closes.** A raw String read ahead of a name resolving to nothing
   draws the raw class, and the name answers when it stands first. Resolving both sides before
   either read's gates names the missing name for both. -/
example :
    [readView (.compareFields .equal (absolute ["Order"] "RawNote") (absolute ["Order"] "NoSuch")),
      readView (.compareFields .equal (absolute ["Order"] "NoSuch") (absolute ["Order"] "RawNote"))] =
      [.refused (some .rawTypeOperandInvalid), .refused (some .invalidEntity)] := by
  native_decide

/- **A path naming a group draws the group class, a root included**, while an unstarred repeatable
   group meets the reader's missing-star class first. A field resolver reports all three as a name
   resolving to nothing. -/
example :
    [readView (compare .greater (absolute ["Order"] "Ledger") (.number 0)),
      readView (compare .greater (absolute [] "Order") (.number 0)),
      readView (compare .greater (absolute ["Order"] "Items") (.number 0))] =
      [.refused (some .noGroupsAllowed), .refused (some .noGroupsAllowed),
        .refused (some .noWildcard)] := by
  native_decide

/- **Every flat bracket comparison asks the read's gates**, the text-field, Enumeration, clock and
   Base-Year forms as well as the field pair: a group draws the group class on each, a raw String
   and a partially known Date the value classes, and a name resolving to nothing its own class. A
   surface resolving its field without the gates reports a group as a name resolving to nothing and
   a raw or partial read without a class. -/
example :
    let ledger := absolute ["Order"] "Ledger"
    let note := absolute ["Order"] "Note"
    [readView (.compareTextFields .equal (.direct ledger) (.direct note)),
      readView (.compareTextFields .equal (.direct (absolute ["Order"] "RawNote")) (.direct note)),
      readView (.compareTextFields .equal (.direct (absolute ["Order"] "PartialDispatch"))
        (.direct note)),
      readView (.compareEnumeration .equal ledger .stored "x"),
      readView (.compareNow .less .right ledger),
      readView (.compareBaseYear .less .right ledger),
      readView (.compareBaseYearRange .less .right .start ledger),
      readView (compare .equal (absolute ["Order"] "PartialDispatch")
        (dateLiteral dispatchDateComponents 0)),
      readView (.compareFields .less note (absolute ["Order"] "NoSuch"))] =
      [.refused (some .noGroupsAllowed), .refused (some .rawTypeOperandInvalid),
        .refused (some .invalidDateType), .refused (some .noGroupsAllowed),
        .refused (some .noGroupsAllowed), .refused (some .noGroupsAllowed),
        .refused (some .noGroupsAllowed), .refused (some .invalidDateType),
        .refused (some .invalidEntity)] := by
  native_decide

/- **A scalar membership's members are field-value reads, whose gates answer ahead of the subject's
   kind gate and the list's own gates** ([inbound](../../../docs/SOURCES.md#inbound-2026-09-25f-field-value-read)).
   A group member draws the group class against a String and a Number subject, and a raw member the
   raw class against a Boolean subject, beside a Number member and after a repeated member. A
   membership asking its subject's kind, the list's base type or its duplicates first reports
   those, which draw no class here. -/
example :
    let ledger := absolute ["Order"] "Ledger"
    let note := absolute ["Order"] "Note"
    let quantity := absolute ["Order"] "Quantity"
    let rawNote := absolute ["Order"] "RawNote"
    [readView (.stringFieldValueMembership .included note [ledger]),
      readView (.numberFieldValueMembership .included quantity [ledger]),
      readView (.enumerationFieldValueMembership .included (.direct note) [.direct ledger]),
      readView (.stringFieldValueMembership .included (absolute ["Order"] "ExpressShipping") [rawNote]),
      readView (.stringFieldValueMembership .included note [quantity, rawNote]),
      readView (.stringFieldValueMembership .included note [quantity, quantity, rawNote])] =
      [.refused (some .noGroupsAllowed), .refused (some .noGroupsAllowed),
        .refused (some .noGroupsAllowed), .refused (some .rawTypeOperandInvalid),
        .refused (some .rawTypeOperandInvalid), .refused (some .rawTypeOperandInvalid)] := by
  native_decide

/- **A scalar membership against literals asks its subject's group gate first**, having no members to
   wait for ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   a fixed group, a bare name naming one and a root draw the group class and an unstarred repeatable
   group the missing-star class. The Kernel's one construct covers the String, Number and Enumeration
   literal forms this surface splits by kind. A field resolver reports every row as a name resolving
   to nothing. -/
example :
    let ledger := absolute ["Order"] "Ledger"
    let items := absolute ["Order"] "Items"
    let root := absolute [] "Order"
    [readView (.stringValueMembership .included ledger ["a"]),
      readView (.stringValueMembership .included items ["a"]),
      readView (.stringValueMembership .included root ["a"]),
      readView (.stringValueMembership .included (bare "Ledger") ["a"]),
      readView (.numberValueMembership .included ledger [1]),
      readView (.numberValueMembership .included items [1]),
      readView (.numberValueMembership .included root [1]),
      readView (.enumerationValueMembership .included (.direct ledger) ["a"]),
      readView (.enumerationValueMembership .included (.direct items) ["a"])] =
      [.refused (some .noGroupsAllowed), .refused (some .noWildcard),
        .refused (some .noGroupsAllowed), .refused (some .noGroupsAllowed),
        .refused (some .noGroupsAllowed), .refused (some .noWildcard),
        .refused (some .noGroupsAllowed), .refused (some .noGroupsAllowed),
        .refused (some .noWildcard)] := by
  native_decide

/- **`Length`'s parameter asks the group gate alone**
   ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)):
   an unstarred repeatable group draws the missing-star class and a fixed group the group class on
   either side of the comparison, and a name resolving to nothing its own class. A raw String and a
   partially known Date meet `Length`'s own gates, which draw no class here, where the read's value
   gates would draw the raw and the date class. -/
example :
    let two : DecodedNumericLiteral := { value := 2, authoredScale := 0 }
    [readView (.lengthCompare .greater (absolute ["Order"] "Items") two),
      readView (.literalCompareLength two .less (absolute ["Order"] "Ledger")),
      readView (.lengthCompare .greater (absolute ["Order"] "NoSuch") two),
      readView (.lengthCompare .greater (absolute ["Order"] "RawNote") two),
      readView (.lengthCompare .greater (absolute ["Order"] "PartialDispatch") two)] =
      [.refused (some .noWildcard), .refused (some .noGroupsAllowed), .refused (some .invalidEntity),
        .refused none, .refused none] := by
  native_decide

/- **A multi-field list's group operand is expanded by the Kernel**, which then reports the base-type
   class of the group's fields beside the String
   ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
   This route cannot expand a group and refuses without a class, where the group class would be the
   wrong claim. -/
example :
    readView (.stringValueList .atLeastOne [absolute ["Order"] "Ledger", absolute ["Order"] "Note"] ["a"]) =
      .refused none := by
  native_decide

/- **A bare name naming a group of the declaring group is a group read, whether one field elsewhere
   shares the name or two do.** The reader takes no short-name fallback for a name its declaring group
   declares ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)),
   so the bracket read and the presence operand both draw the group class. Falling back binds the one
   String field, which the presence operand admits, and displacing only a name resolving to nothing
   leaves two fields on the ambiguity class. `Length`'s parameter asks the same group gate, so the
   bare name draws the group class there too, as an absolute path naming a group does
   ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
example :
    let unique : FlatModel := { readModel with
      fields := readModel.fields ++ [{ noteDecl with id := 30, groupPath := ["Reference"], name := "Ledger" }] }
    let ambiguous : FlatModel := { unique with
      fields := unique.fields ++ [{ noteDecl with id := 31, groupPath := ["Order", "Details"], name := "Ledger" }] }
    [readViewIn unique (compare .greater (bare "Ledger") (.number 0)),
      readViewIn unique (.fieldFilled (bare "Ledger")),
      readViewIn ambiguous (compare .greater (bare "Ledger") (.number 0)),
      readViewIn ambiguous (.fieldFilled (bare "Ledger")),
      readViewIn unique (.lengthCompare .greater (bare "Ledger") { value := 2, authoredScale := 0 })] =
      List.replicate 5 (.refused (some .noGroupsAllowed)) := by
  native_decide

end A12Kernel.Conformance.Elaboration.Static
