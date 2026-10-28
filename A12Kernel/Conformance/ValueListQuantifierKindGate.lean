import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TokenEntityValueList

/-! # A12Kernel.Conformance.ValueListQuantifierKindGate — which field kinds a String-literal value list admits

The three plural value-list quantifiers compare a field list against String literals, and their
kind gate partitions **three** ways rather than two. That third class is invisible to a reading
that sorts kinds into admitted and refused, and it is the operator's own message vocabulary that
makes it legible: a Number field is *inside* the set `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` names,
so it passes that gate and then fails the **literal** comparison with
`MVK_INVALID_TYPES_FOR_COMPARISON`, where DATE, BOOLEAN, DATE_RANGE and CONFIRM never reach that
stage ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
Collapsing the two would report the admitted-set class for a kind the Kernel calls admitted.

The kind rows use same-kind **pairs**, which reach that gate without arguing with the arity one.
The arity rows below are the separate measured fact: the Kernel admits a sole field here and refuses
one at the entity-list carriers, so the shared shape takes its arity rule as an argument rather than
applying one gate to both.
-/

namespace A12Kernel.Conformance.ValueListQuantifierKindGate

open A12Kernel

/-- One declaration per kind the gate can receive, in same-kind pairs. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe"], name := "Email",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Probe"], name := "Phone",
        policy := { kind := .string } },
      { id := 3, groupPath := ["Probe"], name := "AVal",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 4, groupPath := ["Probe"], name := "BVal",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 5, groupPath := ["Probe"], name := "ReportedOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 6, groupPath := ["Probe"], name := "SettledOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 7, groupPath := ["Probe"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 8, groupPath := ["Probe"], name := "Flag2",
        policy := { kind := .boolean } },
      { id := 9, groupPath := ["Probe"], name := "Agreed",
        policy := { kind := .confirm } },
      { id := 10, groupPath := ["Probe"], name := "Agreed2",
        policy := { kind := .confirm } },
      { id := 11, groupPath := ["Probe"], name := "Span",
        policy := { kind := .dateRange },
        dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 12, groupPath := ["Probe"], name := "Span2",
        policy := { kind := .dateRange },
        dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 13, groupPath := ["Probe"], name := "Choice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } },
      { id := 14, groupPath := ["Probe"], name := "Choice2",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } },
      -- A **disjoint** third domain. Without it the two enum fields above share one domain, and a
      -- union rule is indistinguishable from an every-domain one on every row they can form.
      { id := 15, groupPath := ["Probe"], name := "Choice3",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["C", "D"] } },
      -- The three temporal kinds the original rows left out. All four temporal kinds share one
      -- `FieldKind` constructor, so a partition keyed on it needs each of them measured.
      { id := 16, groupPath := ["Probe"], name := "StartsAt",
        policy := { kind := .temporal .time TemporalComponents.time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 17, groupPath := ["Probe"], name := "EndsAt",
        policy := { kind := .temporal .time TemporalComponents.time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 18, groupPath := ["Probe"], name := "SeenAt",
        policy := { kind := .temporal .dateTime TemporalComponents.now },
        temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 19, groupPath := ["Probe"], name := "LeftAt",
        policy := { kind := .temporal .dateTime TemporalComponents.now },
        temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 20, groupPath := ["Probe"], name := "AnniversaryA",
        policy := { kind := .temporal .date { year := false, month := true, day := true, hour := false, minute := false, second := false } },
        temporalTargetPolicy := some { format := "MM-dd" } },
      { id := 21, groupPath := ["Probe"], name := "AnniversaryB",
        policy := { kind := .temporal .date { year := false, month := true, day := true, hour := false, minute := false, second := false } },
        temporalTargetPolicy := some { format := "MM-dd" } },
      { id := 22, groupPath := ["Probe"], name := "SerialA",
        policy := { kind := .string }, customType := some { name := "PolicySerial" } },
      { id := 23, groupPath := ["Probe"], name := "SerialB",
        policy := { kind := .string }, customType := some { name := "PolicySerial" } }] }

example : probeModel.validate.isOk = true := by native_decide

private inductive Admission where
  | admitted
  | refused (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Probe"], field := name }

private def pairAdmission (a b : String) (quantifier : ValueListQuantifier := .atLeastOne) :
    Admission :=
  match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      { quantifier
        fields := { first := field a, rest := [field b] }
        values := ["x", "y"] } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/- The admitted kind, which keeps the refusals below from reading as "this operator refuses
   fields". -/
example : pairAdmission "Email" "Phone" = .admitted := by native_decide

/-- **The admitted set has four members, and the diagnostic's name lists three.** A CUSTOM slot is
admitted here, measured by a12-dmkits on all three slot shapes, so
`MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` is a misleading oracle for the set it appears to enumerate: a
consumer deriving the admitted kinds from the code's name refuses a legal slot.

This project reaches the right answer by construction rather than by a rule of its own, and the case
is worth keeping for exactly that reason. A custom declaration must carry the String kind —
`customTypeRequiresString` — so a CUSTOM field's `policy.kind` *is* `.string` and the slot predicate
never sees a distinct kind to classify. The same construction is what makes the Kernel admit it, its
string-likeness test taking a predefined type. An assumption that happens to hold produces no signal,
so the row is asserted here beside the ordinary String control it must not be confused with. -/
example : pairAdmission "SerialA" "SerialB" = .admitted ∧
    pairAdmission "SerialA" "Email" = .admitted := by native_decide

/- The middle class: admitted by the kind gate, refused by the literal comparison. -/
example :
    pairAdmission "AVal" "BVal" = .refused (some .invalidTypesForComparison) := by
  native_decide

/- The four kinds outside the admitted set, which never reach that comparison. Asserted together
   because the property is that they share one class, not that each has one. -/
example :
    [pairAdmission "ReportedOn" "SettledOn", pairAdmission "Flag" "Flag2",
      pairAdmission "Span" "Span2", pairAdmission "Agreed" "Agreed2"] =
      List.replicate 4 (.refused (some .onlyStringEnumNumberAllowed)) := by
  native_decide

/- **The other three temporal kinds join them**, measured rather than inherited from DATE: TIME,
   DATETIME, and a component-omitting DATEFRAGMENT declaration each draw the same class at this
   slot. They share one `FieldKind` constructor with DATE, so without these rows a partition written
   over that constructor would be right by luck on three quarters of its own arm. -/
example :
    [pairAdmission "StartsAt" "EndsAt", pairAdmission "SeenAt" "LeftAt",
      pairAdmission "AnniversaryA" "AnniversaryB"] =
      List.replicate 3 (.refused (some .onlyStringEnumNumberAllowed)) := by
  native_decide

/-! ### The same gate at a group slot

A group declares no kind of its own, so it reaches this gate through its expansion. The Kernel's
answer is the slot-shape-independent one: a homogeneous group draws exactly what the same kind
draws as a field pair or as a sole field.
-/

private def kindGroupField (id : FieldId) (group : String) (name : String)
    (kind : FieldKind) : FlatFieldDecl :=
  { id, groupPath := ["Bag", group], name, policy := { kind } }

private def dateFragmentComponents : TemporalComponents :=
  { year := false, month := true, day := true, hour := false, minute := false, second := false }

private def groupModel : FlatModel :=
  { fields := [
      kindGroupField 1 "StrG" "A" .string, kindGroupField 2 "StrG" "B" .string,
      kindGroupField 3 "NumG" "A" (.number { scale := 0, signed := false }),
      kindGroupField 4 "NumG" "B" (.number { scale := 0, signed := false }),
      kindGroupField 7 "BoolG" "A" .boolean, kindGroupField 8 "BoolG" "B" .boolean,
      kindGroupField 9 "ConfG" "A" .confirm, kindGroupField 10 "ConfG" "B" .confirm,
      { id := 11, groupPath := ["Bag", "RangeG"], name := "A", policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 12, groupPath := ["Bag", "RangeG"], name := "B", policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 13, groupPath := ["Bag", "EnumG"], name := "A", policy := { kind := .enumeration }, enumeration := some { storedTokens := ["A", "B"] } },
      { id := 14, groupPath := ["Bag", "EnumG"], name := "B", policy := { kind := .enumeration }, enumeration := some { storedTokens := ["A", "B"] } },
      { id := 15, groupPath := ["Bag", "DateG"], name := "A", policy := { kind := .temporal .date TemporalComponents.fullDate }, temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 16, groupPath := ["Bag", "DateG"], name := "B", policy := { kind := .temporal .date TemporalComponents.fullDate }, temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 17, groupPath := ["Bag", "TimeG"], name := "A", policy := { kind := .temporal .time TemporalComponents.time }, temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 18, groupPath := ["Bag", "TimeG"], name := "B", policy := { kind := .temporal .time TemporalComponents.time }, temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 19, groupPath := ["Bag", "DtG"], name := "A", policy := { kind := .temporal .dateTime TemporalComponents.now }, temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 20, groupPath := ["Bag", "DtG"], name := "B", policy := { kind := .temporal .dateTime TemporalComponents.now }, temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 21, groupPath := ["Bag", "FragG"], name := "A", policy := { kind := .temporal .date dateFragmentComponents }, temporalTargetPolicy := some { format := "MM-dd" } },
      { id := 22, groupPath := ["Bag", "FragG"], name := "B", policy := { kind := .temporal .date dateFragmentComponents }, temporalTargetPolicy := some { format := "MM-dd" } },
      -- The repeatable arm of the 2x2 below: same two kinds, differing from their twins above in
      -- repeatability alone, so kind and scope vary independently within one model.
      { id := 23, groupPath := ["Bag", "RepStrG"], name := "A", policy := { kind := .string }, repeatableScope := [40] },
      { id := 24, groupPath := ["Bag", "RepStrG"], name := "B", policy := { kind := .string }, repeatableScope := [40] },
      { id := 25, groupPath := ["Bag", "RepNumG"], name := "A", policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [41] },
      { id := 26, groupPath := ["Bag", "RepNumG"], name := "B", policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [41] }]
    repeatableGroups := [
      { level := 40, path := ["Bag", "RepStrG"], repeatability := some 50 },
      { level := 41, path := ["Bag", "RepNumG"], repeatability := some 50 }] }

example : groupModel.validate.isOk = true := by native_decide

private def groupAdmissionWith (group : String) (values : List String) : Admission :=
  match elaborateTokenEntityStringLiteralValueListSource groupModel ["Bag"]
      { quantifier := .atLeastOne
        fields := { first := .group (.path { base := .absolute, groups := ["Bag", group] }), rest := [] }
        values := values } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/-- The literals are outside every declared Enumeration domain in this fixture, which is what the
    kind rows want: they must be decided by the slot's kind, never by a literal that happens to be a
    declared token. The Enumeration row below supplies its own declared literals for that reason. -/
private def groupAdmission (group : String) : Admission :=
  groupAdmissionWith group ["x", "y"]

private def starredGroupAdmission (group : String) : Admission :=
  match elaborateTokenEntityStringLiteralValueListSource groupModel ["Bag"]
      { quantifier := .atLeastOne
        fields := { first := .starredGroup { base := .absolute, groups := [{ name := "Bag" }, { name := group, starred := true }] }, rest := [] }
        values := ["x", "y"] } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/-- **A scope gate outranks the kind gate, so every kind row above holds only once the level is
bound.** This is the 2×2 that separates them: the two repeatable groups differ from their
non-repeatable twins in repeatability alone, and the two kinds are one admitted and one refused, so
scope and kind vary independently inside one model.

Read down the scope axis and the kind gate is silent — an unstarred repeatable level draws
`MVK_NO_WILDCARD` whether its expansion is String or Number, which is what "outranks" means. Read
across the bound row and the kind gate answers exactly as it does on a non-repeatable carrier.

The confound this removes was real and was in this module: every group in the fixture was
non-repeatable, and none of the kind rows said so, so the whole set was consistent with an account
that never mentions scope. a12-dmkits found it in a cold review of their own slice after publishing
the kind denominator to this project, and the repeatable rows here reproduce their grid. The
denominator and the four-member admitted set are unchanged by it; only the scope at which they hold
was missing (`SPEC-2026-09-22-03`). -/
example :
    (groupAdmission "RepStrG", starredGroupAdmission "RepStrG") =
      (.refused (some .noWildcard), .admitted) ∧
    (groupAdmission "RepNumG", starredGroupAdmission "RepNumG") =
      (.refused (some .noWildcard), .refused (some .invalidTypesForComparison)) ∧
    (groupAdmission "StrG", groupAdmission "NumG") =
      (.admitted, .refused (some .invalidTypesForComparison)) := by
  native_decide

/-- **Every kind outside the admitted set draws the class at a group slot too**, which this carrier
previously reported for DATE alone — the other five reached no class at all, because a group's
expansion is erased before the certification that classifies a direct field. The six rows are
asserted together because the property is that the slot shape does not matter, not that each kind
has an answer ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-slot-kind-set)). -/
example :
    ["DateG", "TimeG", "DtG", "FragG", "RangeG", "BoolG"].map groupAdmission =
      List.replicate 6 (.refused (some .onlyStringEnumNumberAllowed)) ∧
      groupAdmission "ConfG" = .refused (some .onlyStringEnumNumberAllowed) := by
  native_decide

/-- The admitted side, which keeps the six rows above from reading as "a group slot is refused".
`NumG` is the separator that fixes *which* gate answered: it is inside the admitted set, so it
passes this gate and falls to the literal comparison exactly as the Number field pair does. -/
example :
    groupAdmission "StrG" = .admitted ∧
      groupAdmissionWith "EnumG" ["A", "B"] = .admitted ∧
      groupAdmission "NumG" = .refused (some .invalidTypesForComparison) := by
  native_decide

private def enumAdmission (values : List String) : Admission :=
  match values with
  | [] => .refused none
  | firstValue :: restValues =>
      match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
          { quantifier := .atLeastOne
            fields := { first := field "Choice", rest := [field "Choice2"] }
            values := firstValue :: restValues } with
      | .ok _ => .admitted
      | .error error => .refused error.diagnostic?

/- **An Enumeration field side is legal against String literals**, and the gate is on the literal's
   **value** rather than on the field's kind — the one place a value list's own literals are
   constrained statically. Declared tokens are admitted; a literal naming none draws the Kernel's
   own class. The pair is what makes this a value gate: without the admitted row the refusal would
   read as this operator rejecting Enumeration outright, which is what this project used to do. -/
example : (enumAdmission ["A", "B"], enumAdmission ["A"], enumAdmission ["x", "y"],
    enumAdmission ["A", "x"]) =
    (.admitted, .admitted,
      .refused (some .invalidStringConstantForEnumerationOrCategory),
      .refused (some .invalidStringConstantForEnumerationOrCategory)) := by
  native_decide

/- One undeclared literal beside a declared one is enough, which is the row that keeps the gate from
   reading as "at least one literal must be a token". -/
example : pairAdmission "Choice" "Choice2" =
    .refused (some .invalidStringConstantForEnumerationOrCategory) := by native_decide

private def disjointAdmission (values : List String) : Admission :=
  match values with
  | [] => .refused none
  | firstValue :: restValues =>
      match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
          { quantifier := .atLeastOne
            fields := { first := field "Choice", rest := [field "Choice3"] }
            values := firstValue :: restValues } with
      | .ok _ => .admitted
      | .error error => .refused error.diagnostic?

/- **The domain a literal must name is the UNION of the selected fields' domains, not every one.**
   Over disjoint `{A,B}` and `{C,D}`: a literal from either side alone is admitted, one from each is
   admitted together, and only a literal in neither is refused. This project required membership in
   *every* selected domain until it was measured, which refused all three admitted rows here — the
   conservative side, but the wrong one. The disjointness is what separates the accounts; on the
   equal-domain pair above, union and intersection agree on every row. -/
example : (disjointAdmission ["A"], disjointAdmission ["C"], disjointAdmission ["A", "C"],
    disjointAdmission ["Z"]) =
    (.admitted, .admitted, .admitted,
      .refused (some .invalidStringConstantForEnumerationOrCategory)) := by
  native_decide

private def repeatedRefAdmission : Admission :=
  match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      { quantifier := .atLeastOne
        fields := { first := field "Choice", rest := [field "Choice"] }
        values := ["A"] } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/- The same **unstarred** reference twice draws `MVK_DUPLICATE_PARAM1` at this carrier as at the
   entity-list ones, measured on all four together; the starred form of the same repetition is
   admitted and is the shared shape's own row. The literal is a **declared** token here on purpose:
   with an undeclared one the row would refuse for the value reason and establish nothing about
   repetition. -/
example : repeatedRefAdmission = .refused (some .duplicateParam1) := by
  native_decide

private def soleAdmission (quantifier : ValueListQuantifier) (name : String) :
    Admission :=
  match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
      { quantifier, fields := { first := field name, rest := [] }
        values := ["x", "y"] } with
  | .ok _ => .admitted
  | .error error => .refused error.diagnostic?

/- **A sole unstarred field is legal at all three quantifiers**, and refused at the entity-list
   carriers on the same fixture. The arity rule is per carrier, so the shared shape now takes it as
   an argument instead of applying one gate to both; this row is what that argument is for. -/
example : [ValueListQuantifier.atLeastOne, .no, .notAll].map
    (soleAdmission · "Email") = List.replicate 3 Admission.admitted := by
  native_decide

/- The other side of the same argument, on the carrier measured to refuse. Without it the row above
   would be equally well explained by this project having dropped the arity gate altogether, which
   is the mistake the shared checker's single rule was protecting against. -/
example :
    (match elaborateTokenDistinctCountSource probeModel ["Probe"]
        { first := field "Email", rest := [] } with
      | .ok _ => Admission.admitted
      | .error error => Admission.refused error.diagnostic?) =
      .refused (some .paramSizeInvalidN) := by
  native_decide

/- The kind gate still fires under the relaxed arity: a sole Number field reaches the literal
   comparison exactly as the pair does, so widening the arity did not widen anything else. -/
example : soleAdmission .atLeastOne "AVal" =
    .refused (some .invalidTypesForComparison) := by
  native_decide

/-! ### The base-type gate ahead of the kind gate

The quantifiers ask whether every field shares one base type before they ask whether each is a
kind they admit, so a list mixing base types draws `MVK_VARYING_TYPES_NOT_ALLOWED` whatever its
kinds. The four temporal kinds share one base type and a custom declaration shares String's
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-value-list-base-type)).
-/

/- **A mixed list draws the base-type class ahead of the kind gate.** A String beside a Number, on
   two quantifiers (the inbound above), and a String beside a Date
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
   Read by the kind gate, the first draws the literal comparison's class, and the last the kind
   gate's. -/
example :
    [pairAdmission "Email" "AVal", pairAdmission "Email" "AVal" .no,
      pairAdmission "Email" "ReportedOn"] =
      List.replicate 3 (.refused (some .varyingTypesNotAllowed)) := by
  native_decide

/- **Two temporal kinds share one base type**, so a Date beside a date fragment and a Time beside a
   DateTime pass that gate and meet the kind gate, as two Dates do. A partition keyed on the temporal
   family draws the base-type class for the Time beside the DateTime. The fragment carries the Date's
   family here, so only that second pair separates such a partition. -/
example :
    [pairAdmission "ReportedOn" "AnniversaryA", pairAdmission "StartsAt" "SeenAt"] =
      List.replicate 2 (.refused (some .onlyStringEnumNumberAllowed)) := by
  native_decide

/- **Every cross pair differs, whichever kind comes first**
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-base-type-cross-pairs)). An Enumeration beside a
   String in both orders, a Boolean beside a Confirm in both orders, a Number beside a Date or before
   a String, a date range beside a String and a Boolean beside a Date. The Boolean pairs are what
   separate this gate from the kind gate, which refuses both kinds with one class, and the
   Enumeration pair from a gate merging the two token families. -/
example :
    [pairAdmission "Choice" "Email", pairAdmission "Email" "Choice", pairAdmission "Flag" "Agreed",
      pairAdmission "Agreed" "Flag", pairAdmission "AVal" "ReportedOn", pairAdmission "Span" "Email",
      pairAdmission "AVal" "Email", pairAdmission "Flag" "ReportedOn"] =
      List.replicate 8 (.refused (some .varyingTypesNotAllowed)) := by
  native_decide

private def entityAdmissionIn (model : FlatModel) (fields values : List SurfaceFieldEntityOperand) :
    Admission :=
  match fields, values with
  | fieldFirst :: fieldRest, valueFirst :: valueRest =>
      match elaborateTokenEntityValueListSource model ["Probe"]
          { quantifier := .atLeastOne
            fields := { first := fieldFirst, rest := fieldRest }
            values := { first := valueFirst, rest := valueRest } } with
      | .ok _ => .admitted
      | .error error => .refused error.diagnostic?
  | _, _ => .refused none

private def entityAdmission (fields values : List String) : Admission :=
  entityAdmissionIn probeModel (fields.map field) (values.map field)

/- **The value list is matched against the first field's base type.** A String value list is
   admitted opposite a String field. A Number or an Enumeration value draws the base-type class, so
   does a String value opposite an Enumeration field, and so does a Time value after a sound String
   one. The same declaration on both sides draws the duplicate class. -/
example :
    [entityAdmission ["Email"] ["Phone"], entityAdmission ["Email"] ["AVal"],
      entityAdmission ["Email"] ["Choice"], entityAdmission ["Choice"] ["Email"],
      entityAdmission ["Choice"] ["AVal"], entityAdmission ["Email"] ["Phone", "StartsAt"],
      entityAdmission ["Email"] ["Email"]] =
      [.admitted, .refused (some .varyingTypesNotAllowed), .refused (some .varyingTypesNotAllowed),
        .refused (some .varyingTypesNotAllowed), .refused (some .varyingTypesNotAllowed),
        .refused (some .varyingTypesNotAllowed), .refused (some .duplicateParam1)] := by
  native_decide

/- The field list of the entity form meets the same two gates first. A mixed field list draws the
   base-type class, and two Dates the kind gate's. A Number field is inside the kind set, so its value
   side is read next and a String value there draws the base-type class. Number values opposite it
   claim no class: this token fragment refuses them, and no literal stands opposite for the
   comparison class to read. -/
example :
    [entityAdmission ["Email", "AVal"] ["Phone"], entityAdmission ["ReportedOn", "SettledOn"] ["Phone"],
      entityAdmission ["AVal"] ["Email"], entityAdmission ["AVal"] ["BVal"]] =
      [.refused (some .varyingTypesNotAllowed), .refused (some .onlyStringEnumNumberAllowed),
        .refused (some .varyingTypesNotAllowed), .refused none] := by
  native_decide

/- **A repeat across the two lists is asked after the base-type and kind gates, and a repeat within
   the field list before them** ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-value-list-cross-list-repeat-order)).
   A field named again among the values draws the field list's base-type class, the kind gate's
   class, or the value side's base-type class, whichever of them its lists fail. A field named twice
   among the fields draws the duplicate class ahead of the base-type class the same list fails. A
   repeat that pre-empted every gate would draw the duplicate class for all four. -/
example :
    [entityAdmission ["Email", "AVal"] ["Email"], entityAdmission ["ReportedOn"] ["ReportedOn"],
      entityAdmission ["Email"] ["Email", "AVal"]] =
      [.refused (some .varyingTypesNotAllowed), .refused (some .onlyStringEnumNumberAllowed),
        .refused (some .varyingTypesNotAllowed)] ∧
    (match elaborateTokenEntityStringLiteralValueListSource probeModel ["Probe"]
        { quantifier := .atLeastOne
          fields := { first := field "Email", rest := [field "Email", field "AVal"] }
          values := ["x"] } with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .duplicateParam1 := by
  native_decide

/-- The probe model plus a String waiving value validation and a fixed group holding one String. -/
private def validationModel : FlatModel :=
  { probeModel with
    fields := probeModel.fields ++ [
      { id := 24, groupPath := ["Probe"], name := "Memo", policy := { kind := .string },
        stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } },
      { id := 25, groupPath := ["Probe", "Recipient"], name := "RecipientName",
        policy := { kind := .string } }] }

/- **Value validation is the value-list construct's fourth gate, and a repeat across the two lists
   comes between its two askings** ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25g-value-list-order)).
   The field list's value validation follows its kind gate, ahead of a value list's own repeat or
   base type; the cross-list repeat follows both lists' type gates; the value list's value validation
   comes last. So a raw String repeated across the lists, one opposite a Number, one among the values
   and one against a literal draw the raw class, a value list's own repeat draws the duplicate class
   ahead of its base type, a cross-list repeat beside a raw value draws the duplicate class, and a
   group opposite its own field draws the containment class. -/
example :
    let group : SurfaceFieldEntityOperand := .group (.path { base := .absolute, groups := ["Probe", "Recipient"] })
    let recipientName : SurfaceFieldEntityOperand :=
      .field { base := .absolute, groups := ["Probe", "Recipient"], field := "RecipientName" }
    let admission (fields values : List String) :=
      entityAdmissionIn validationModel (fields.map field) (values.map field)
    [admission ["Memo"] ["Memo"], admission ["Memo"] ["AVal"], admission ["Email"] ["Memo"],
      admission ["Email"] ["Email", "Memo"], admission ["Email"] ["AVal", "AVal"],
      entityAdmissionIn validationModel [group] [recipientName]] =
      [.refused (some .rawTypeOperandInvalid), .refused (some .rawTypeOperandInvalid),
        .refused (some .rawTypeOperandInvalid), .refused (some .duplicateParam1),
        .refused (some .duplicateParam1), .refused (some .duplicateParam2)] ∧
    (match elaborateTokenEntityStringLiteralValueListSource validationModel ["Probe"]
        { quantifier := .atLeastOne, fields := { first := field "Memo", rest := [] }, values := ["x"] } with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .rawTypeOperandInvalid := by
  native_decide

/- A Number field list is inside the kind set, so a Number repeated across the lists reaches the
   cross-list repeat and draws the duplicate class, on the String and Date rows' account: no row
   repeats a Number across the lists. A value-side name resolving to nothing answers ahead
   of the field list's value validation
   ([checkpoint](../../docs/sources/field-value-read-probes.md#src-field-value-read-predictions)),
   where asking the field list's gates first draws the raw class. -/
example :
    [entityAdmissionIn validationModel [field "AVal"] [field "AVal"],
      entityAdmissionIn validationModel [field "Memo"] [field "NoSuch"]] =
      [.refused (some .duplicateParam1), .refused (some .invalidEntity)] := by
  native_decide

/-- The validation model plus an Enumeration declaring a category, a fixed group holding a String and
    a Date, a fixed group holding a Number, and a repeatable group holding a String. -/
private def readGateModel : FlatModel :=
  { validationModel with
    fields := validationModel.fields ++ [
      { id := 26, groupPath := ["Probe"], name := "Grade", policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"], categories := [{ name := "Band", tokens := ["Hi", "Lo"] }] } },
      { id := 27, groupPath := ["Probe", "Mix"], name := "MixText", policy := { kind := .string } },
      { id := 28, groupPath := ["Probe", "Mix"], name := "MixDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 29, groupPath := ["Probe", "Ledger"], name := "Total",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 30, groupPath := ["Probe", "Items"], name := "Label", policy := { kind := .string },
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Items"] }] }

/- **A group operand is expanded and a category read is an Enumeration, both ahead of the base-type
   gate** ([checkpoint](../../docs/sources/field-value-read-probes.md#src-field-value-read-predictions)).
   A group holding a String and a Date, on either side, and a group holding a Number opposite a String
   draw the base-type class. A category read of an Enumeration opposite a String draws it too, while a
   raw String ahead of that category draws the raw class, the field list's value validation answering
   first. A name resolving to nothing answers on either side. -/
example :
    let group (name : String) : SurfaceFieldEntityOperand :=
      .group (.path { base := .absolute, groups := ["Probe", name] })
    let category (name : String) : SurfaceFieldEntityOperand :=
      .field { base := .absolute, groups := ["Probe"], field := name } (.projected "Band")
    [entityAdmissionIn readGateModel [field "NoSuch"] [field "Memo"],
      entityAdmissionIn readGateModel [field "Email"] [group "Mix"],
      entityAdmissionIn readGateModel [group "Mix"] [field "Email"],
      entityAdmissionIn readGateModel [field "Email"] [group "Ledger"],
      entityAdmissionIn readGateModel [category "Grade"] [field "Memo"],
      entityAdmissionIn readGateModel [field "Memo"] [category "Grade"],
      entityAdmissionIn readGateModel [category "Grade"] [field "Email"]] =
      [.refused (some .invalidEntity), .refused (some .varyingTypesNotAllowed),
        .refused (some .varyingTypesNotAllowed), .refused (some .varyingTypesNotAllowed),
        .refused (some .varyingTypesNotAllowed), .refused (some .rawTypeOperandInvalid),
        .refused (some .varyingTypesNotAllowed)] := by
  native_decide

/- **A category read of a field declaring no Enumeration draws its own class**, on the stored form
   and on a starred operand of the projected form
   ([checkpoint](../../docs/sources/field-value-read-probes.md#src-field-value-read-predictions)).
   The starred row is measured against a literal, which the projected form does not carry, and each
   measured row's value side is clean, so no row orders the category read against a failing value.
   The projected form's direct category arm answers the same class. A token list reading the field
   stored instead admits the first row. -/
example :
    let star : SurfaceStarFieldPath :=
      { base := .absolute, groups := [{ name := "Probe" }, { name := "Items", starred := true }],
        field := "Label" }
    let email : SurfaceTextFieldOperand := .direct { base := .absolute, groups := ["Probe"], field := "Email" }
    entityAdmissionIn readGateModel [.field { base := .absolute, groups := ["Probe"], field := "Email" }
        (.projected "Band")] [field "Phone"] = .refused (some .noEnumeration) ∧
    (match elaborateProjectedTokenEntityValueListSource readGateModel ["Probe"]
        { quantifier := .atLeastOne, fields := { first := .star star (.category "Band"), rest := [] }
          values := { first := .field email, rest := [] } } with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .noEnumeration ∧
    let emailCategory : SurfaceProjectedTokenEntityOperand :=
      .field (.category { base := .absolute, groups := ["Probe"], field := "Email" } "Band")
    let phone : SurfaceTextFieldOperand := .direct { base := .absolute, groups := ["Probe"], field := "Phone" }
    (match elaborateProjectedTokenEntityValueListSource readGateModel ["Probe"]
        { quantifier := .atLeastOne, fields := { first := emailCategory, rest := [] }
          values := { first := .field phone, rest := [] } } with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .noEnumeration := by
  native_decide

/- **The stored form keeps a category read's projection**, so the category's own token is a legal
   literal against it and the Enumeration's stored tokens are not, where reading the slot stored
   would decide both the other way ([`spec/06`](../../spec/06-strings-and-enumerations.md)'s union
   rule). A group operand beside a String draws the base-type class on the literal form as it does on
   the field-valued one (row `b8`). -/
example :
    let admits (operand : SurfaceFieldEntityOperand) (literal : String) : Bool :=
      (elaborateTokenEntityStringLiteralValueListSource readGateModel ["Probe"]
        { quantifier := .atLeastOne, fields := { first := operand, rest := [] }, values := [literal] }).isOk
    let category : SurfaceFieldEntityOperand :=
      .field { base := .absolute, groups := ["Probe"], field := "Grade" } (.projected "Band")
    [admits category "Hi", admits category "A", admits (field "Grade") "A", admits (field "Grade") "Hi"] =
      [true, false, true, false] ∧
    let ledger : SurfaceFieldEntityOperand := .group (.path { base := .absolute, groups := ["Probe", "Ledger"] })
    (match elaborateTokenEntityStringLiteralValueListSource readGateModel ["Probe"]
        { quantifier := .atLeastOne, fields := { first := ledger, rest := [field "Email"] }, values := ["a"] } with
      | .ok _ => none
      | .error error => error.diagnostic?) = some .varyingTypesNotAllowed := by
  native_decide

/- **A category the Enumeration does not declare is read with the operand, ahead of the duplicate
   gate**, first or after a repeated String, against a declared category meeting that gate
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26h-list-reads)). -/
example :
    let verdict (fields : SurfaceFieldEntitySource) : Option (Option KernelStaticDiagnostic) :=
      match elaborateTokenEntityStringLiteralValueListSource readGateModel ["Probe"]
          { quantifier := .atLeastOne, fields, values := ["a"] } with
      | .ok _ => none
      | .error error => some error.diagnostic?
    let grade (category : String) : SurfaceFieldEntityOperand :=
      .field { base := .absolute, groups := ["Probe"], field := "Grade" } (.projected category)
    [verdict { first := grade "Nope", rest := [field "Email", field "Email"] },
      verdict { first := field "Email", rest := [field "Email", grade "Nope"] },
      verdict { first := grade "Band", rest := [field "Email", field "Email"] }] =
      [some (some .categoryUnknown), some (some .categoryUnknown), some (some .duplicateParam1)] := by
  native_decide

end A12Kernel.Conformance.ValueListQuantifierKindGate
