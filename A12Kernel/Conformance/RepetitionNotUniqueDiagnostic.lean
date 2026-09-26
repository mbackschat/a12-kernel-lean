import A12Kernel.Elaboration.ValidationRule

/-! # A12Kernel.Conformance.RepetitionNotUniqueDiagnostic — RNU key-admission diagnostic identity

`RepetitionNotUnique` reads its keys, judges the key list gate by gate, then runs one of two
branches, and most of its classes are shared with the group-list families. One separating fact is a
**collapse**: three structurally different shapes draw one Kernel class — a second key in a
nonrepeatable group, a sole key whose group is not repeatable, and the rule already placed at that
repeated group. The local error type is finer than the observable.

The whole-rule error-field reference gate is measured here too, because it is the gate that decides
whether an RNU rule is authorable at all and it is not an operand gate.
-/

namespace A12Kernel.Conformance.RepetitionNotUniqueDiagnostic

open A12Kernel

private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 3, groupPath := ["Probe", "Rows"], name := "RowKey2",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 4, groupPath := ["Probe", "Rows"], name := "RowNum",
        policy := { kind := .number { scale := 0, signed := false } },
        repeatableScope := [10] },
      { id := 5, groupPath := ["Probe", "Coupons"], name := "CouponVal",
        policy := { kind := .string }, repeatableScope := [11] }]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"] },
      { level := 11, path := ["Probe", "Coupons"] }] }

private def indexedProbeModel : FlatModel :=
  { probeModel with repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"], indexField := some 2 },
      { level := 11, path := ["Probe", "Coupons"] }] }

private def key (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def relativeKey (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

/-- The rule reports on a field of `Rows`, as the measured key rows do. -/
private def diagnosticAt (rowGroup : GroupPath) (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := []) : Option KernelStaticDiagnostic :=
  match CheckedValidationCondition.fromRepetitionNotUnique probeModel rowGroup
      { firstKey := first, restKeys := rest } ["Probe", "Rows"] with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => error.diagnostic?
  | .error _ => none

private def diagnostic? (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := []) : Option KernelStaticDiagnostic :=
  diagnosticAt ["Probe"] first rest

private def indexedRnuUse
    (token : String := "SKU-1") : SurfaceRepetitionNotUniqueSemanticIndexUse := {
  target := key ["Probe", "Rows"] "RowVal"
  token
}

private def indexedRnuRefusal?
    (token : String := "SKU-1") :
    Option (CheckedRepetitionNotUniqueSemanticIndexRefusal indexedProbeModel) :=
  (elaborateRepetitionNotUniqueSemanticIndexRefusal indexedProbeModel ["Probe"]
    (indexedRnuUse token) ["Probe", "Rows"]).toOption

private def indexedRnuDiagnostic?
    (sourceModel : FlatModel := indexedProbeModel) : Option KernelStaticDiagnostic :=
  projectRepetitionNotUniqueSemanticIndexDiagnostic? sourceModel ["Probe"]
    (indexedRnuUse "SKU-1") ["Probe", "Rows"]

/- One key repeated draws the exact-duplicate class, the same one a repeated group-list operand
   draws — the operand relation is shared across families rather than restated per operator. -/
example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "Rows"] "RowVal"] =
      some .duplicateParam1 := by
  native_decide

/- The collapse: a second key in a different group and a sole key in a nonrepeatable group are two
   distinct local errors and **one** Kernel class. Projecting them apart would invent a distinction
   the engine does not report. -/
example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "A"] "AVal"] =
      some .repeatableGroupMissing := by
  native_decide

example :
    diagnostic? (key ["Probe", "A"] "AVal") = some .repeatableGroupMissing := by
  native_decide

/- An unresolvable key path takes the resolver's class rather than a key-specific one, and the class
   names the segment that missed, a walk above the root, or a bare name matching several fields
   ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)). -/
example :
    let shortNameModel : FlatModel :=
      { probeModel with
        fields := probeModel.fields ++
          [{ id := 6, groupPath := ["Probe", "A"], name := "RowKey2", policy := { kind := .string } }]
        fieldRefByShortNameAllowed := true }
    diagnostic? (key ["Probe", "Rows"] "Nope") = some .invalidEntity ∧
    diagnostic? (key ["Probe", "Nope"] "RowVal") = some .invalidEntity ∧
    diagnostic? (key ["Nope", "Rows"] "RowVal") = some .invalidRootGroup ∧
    diagnostic? (relativeKey "Nope") = some .invalidEntity ∧
    diagnostic? { base := .relative 1, groups := ["Rows"], field := "RowVal" } =
      some .tooManyParentGroups ∧
    (match CheckedValidationCondition.fromRepetitionNotUnique shortNameModel ["Probe"]
        { firstKey := relativeKey "RowKey2", restKeys := [] } ["Probe", "Rows"] with
      | .error (.repetitionNotUnique error) => error.diagnostic?
      | _ => none) = some .fieldNameNotUnique := by
  native_decide

/- A model that fails validation never reaches the key's resolver projection: the refusal is the
   model's, and no key row measures it. -/
example :
    let invalidModel : FlatModel :=
      { probeModel with
        fields := probeModel.fields.map fun declaration =>
          if declaration.id == 4 then
            { declaration with numericTargetConstraints := { minFractionalDigits := 1 } }
          else declaration }
    (match CheckedValidationCondition.fromRepetitionNotUnique invalidModel ["Probe"]
        { firstKey := key ["Probe", "Rows"] "RowVal", restKeys := [] } ["Probe", "Rows"] with
      | .error (.repetitionNotUnique (.model _)) => true
      | _ => false) = true ∧
    (match CheckedValidationCondition.fromRepetitionNotUnique invalidModel ["Probe"]
        { firstKey := key ["Probe", "Rows"] "RowVal", restKeys := [] } ["Probe", "Rows"] with
      | .error (.repetitionNotUnique error) => error.diagnostic?
      | _ => none) = none := by
  native_decide

/-! ## Accepted controls

Each names a shape the classes above must not claim: one key, two keys in the same repeatable group,
and a Number key — the last because the local error type has an `unsupportedKeyKind` arm whose class
no measured row covers, and Number is measured *admitted*. -/

example : diagnostic? (key ["Probe", "Rows"] "RowVal") = none := by
  native_decide

example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "Rows"] "RowKey2"] =
      none := by
  native_decide

example : diagnostic? (key ["Probe", "Rows"] "RowNum") = none := by
  native_decide

/- The otherwise-valid RNU key and semantic-index selection return the measured carrier refusal and
   its exact external code. -/
example : indexedRnuDiagnostic? = some .semanticIndexNotAllowed ∧
    indexedRnuDiagnostic?.map (·.kernelCode) =
      some "MVK_SEMANTIC_INDEX_NOT_ALLOWED" := by
  native_decide

/- The checked refusal retains one exact field, group, index, and token before projecting that
   refusal. -/
example : indexedRnuRefusal?.map (fun checked =>
    checked.source.firstKey.fieldId) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.targetDeclaration.id) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.indexDeclaration.id) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.group.path) = some ["Probe", "Rows"] ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.key) =
        some (CheckedSemanticIndexKey.literal (.text "SKU-1")) := by
  native_decide

/- The checked refusal retains the caller's exact token rather than specializing the measured
   `SKU-1` row. This is an internal identity guard, not wider Kernel correspondence. -/
example : (indexedRnuRefusal? "SKU-2").map
    (fun checked => checked.selection.key) =
      some (.literal (.text "SKU-2")) := by
  native_decide

/- An unindexed target and a rule already placed at the repeated group do not inherit the measured
   carrier code. The last keeps the otherwise-valid semantic-index side from replacing the RNU
   source check. -/
example : indexedRnuDiagnostic? probeModel = none ∧
    projectRepetitionNotUniqueSemanticIndexDiagnostic? indexedProbeModel
      ["Probe", "Rows"] (indexedRnuUse "SKU-1") ["Probe", "Rows"] = none := by
  native_decide

/- At the repeated rule group, both path spellings draw the third missing-repeatable shape. -/
example :
    diagnosticAt ["Probe", "Rows"] (key ["Probe", "Rows"] "RowVal") =
      some .repeatableGroupMissing ∧
    diagnosticAt ["Probe", "Rows"] (relativeKey "RowVal") =
      some .repeatableGroupMissing := by
  native_decide

/- The upstream index-free parallel fixture reports `MVK_NO_WILDCARD`, the indexed one the
   shared-path class, and what separates them is whether the second key's read passes the walk: from
   a rule reporting in `Rows`, the walk refuses the unpaired `Coupons` read whether the rule sits at
   the root or in `Rows`. -/
example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "Coupons"] "CouponVal"] =
      some .noWildcard ∧
    diagnosticAt ["Probe", "Rows"] (key ["Probe", "Rows"] "RowVal")
        [key ["Probe", "Coupons"] "CouponVal"] =
      some .noWildcard := by
  native_decide

/-! ## The whole-rule error-field reference gate

Not an operand gate: it reads the assembled rule, so it is projected at rule assembly. An RNU rule
whose keys name a sibling rather than the error field draws it, while naming the error field among
the keys is admitted — which is what lets an RNU rule carry an error field inside the iterated row. -/

private def ruleDiagnostic? (errorField : FieldId)
    (first : SurfaceFieldPath) : Option KernelStaticDiagnostic := do
  let condition ← (CheckedValidationCondition.fromRepetitionNotUnique probeModel
    ["Probe"] { firstKey := first, restKeys := [] } ["Probe", "Rows"]).toOption
  match assembleResolvedValidationRule probeModel condition errorField "RNU"
      .error { parts := [] } with
  | .ok _ => none
  | .error error => error.diagnostic?

example :
    ruleDiagnostic? 3 (key ["Probe", "Rows"] "RowVal") =
      some .errorFieldNotReferenced := by
  native_decide

example : ruleDiagnostic? 2 (key ["Probe", "Rows"] "RowVal") = none := by
  native_decide

/-! ## The key list's gates and the two branches

The Kernel reads every key, asks the list's duplicate gate, then judges the key list gate by gate,
each over the whole list, and only then runs one of two branches: with `@From` the scope's gates,
without it the placement gates ([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)).
The carrier mirrors the peer's: `Claims` and `Payments` are keyed on the same index field, so a read
of one from a rule about the other iterates jointly and reaches the placement gates. The rows are
the peer's; its category and starred rows have no spelling here, since a key is a plain field path.
-/

private def policyModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Policy"], name := "Reference", policy := { kind := .string } },
      { id := 2, groupPath := ["Policy"], name := "Memo", policy := { kind := .string },
        stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } },
      { id := 3, groupPath := ["Policy", "Insured"], name := "InsuredName",
        policy := { kind := .string } },
      { id := 4, groupPath := ["Policy", "Claims"], name := "ClaimRef",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 5, groupPath := ["Policy", "Claims"], name := "Amount",
        policy := { kind := .number { scale := 2, signed := true } }, repeatableScope := [10] },
      { id := 6, groupPath := ["Policy", "Claims"], name := "RawNote",
        policy := { kind := .string }, stringValueMode := .raw,
        stringPolicy := { lineBreaksPermitted := true }, repeatableScope := [10] },
      { id := 7, groupPath := ["Policy", "Claims", "Items"], name := "ItemRef",
        policy := { kind := .string }, repeatableScope := [10, 12] },
      { id := 11, groupPath := ["Policy", "Claims", "Detail"], name := "DetailRef",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 12, groupPath := ["Policy", "Claims", "Adjuster"], name := "AdjusterRef",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 13, groupPath := ["Policy", "Claims", "Assessor"], name := "AssessorRef",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 8, groupPath := ["Policy", "Payments"], name := "ClaimRef",
        policy := { kind := .string }, repeatableScope := [11] },
      { id := 9, groupPath := ["Policy", "Payments"], name := "PayRef",
        policy := { kind := .string }, repeatableScope := [11] },
      { id := 10, groupPath := ["Policy", "Notes"], name := "NoteRef",
        policy := { kind := .string }, repeatableScope := [13] },
      { id := 14, groupPath := ["Policy", "Batches", "Items"], name := "LineRef",
        policy := { kind := .string }, repeatableScope := [15, 16] },
      { id := 15, groupPath := ["Policy", "Batches", "Items"], name := "ItemRef",
        policy := { kind := .string }, repeatableScope := [15, 16] },
      { id := 16, groupPath := ["Policy", "Batches", "Parts"], name := "LineRef",
        policy := { kind := .string }, repeatableScope := [15, 17] },
      { id := 17, groupPath := ["Policy", "Batches", "Parts"], name := "PartRef",
        policy := { kind := .string }, repeatableScope := [15, 17] }]
    repeatableGroups := [
      { level := 10, path := ["Policy", "Claims"], indexField := some 4 },
      { level := 12, path := ["Policy", "Claims", "Items"] },
      { level := 11, path := ["Policy", "Payments"], indexField := some 8 },
      { level := 13, path := ["Policy", "Notes"] },
      { level := 14, path := ["Policy", "Vacant"] },
      { level := 15, path := ["Policy", "Batches"] },
      { level := 16, path := ["Policy", "Batches", "Items"], indexField := some 14 },
      { level := 17, path := ["Policy", "Batches", "Parts"], indexField := some 16 }] }

private def rel (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups, field }

private def fromGroups (groups : List String) : SurfaceRepetitionNotUniqueScope :=
  .from (.path { base := .relative 0, groups })

/-- The rule sits in `rowGroup` and reports on a field of `writtenGroup`: `none` when admitted,
    otherwise the refusal's class. -/
private def policyVerdict (rowGroup writtenGroup : GroupPath) (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath := []) (scope : SurfaceRepetitionNotUniqueScope := .default) :
    Option (Option KernelStaticDiagnostic) :=
  match CheckedValidationCondition.fromRepetitionNotUnique policyModel rowGroup
      { firstKey := first, restKeys := rest, scope } writtenGroup with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => some error.diagnostic?
  | .error _ => some none

/-- The peer's default carrier: the rule at the root reporting on `Claims/ClaimRef`. -/
private def atRoot (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := [])
    (scope : SurfaceRepetitionNotUniqueScope := .default) :
    Option (Option KernelStaticDiagnostic) :=
  policyVerdict ["Policy"] ["Policy", "Claims"] first rest scope

/- The key list, one gate per row. A root group is one more group to this list, since the carrier
   asks no root-group gate. -/
example :
    atRoot (rel ["Claims"] "ClaimRef") = none ∧
    atRoot (rel [] "Claims") = some (some .noGroupsAllowed) ∧
    atRoot (key [] "Policy") = some (some .noGroupsAllowed) ∧
    atRoot (rel ["Claims"] "RawNote") = some (some .rawTypeOperandInvalid) := by
  native_decide

/- A semantic index on a key other than the error field is refused too: here the key is `Amount`
   and the error field `ClaimRef`. -/
example :
    projectRepetitionNotUniqueSemanticIndexDiagnostic? policyModel ["Policy"]
      { target := rel ["Claims"] "Amount", token := "C-1" } ["Policy", "Claims"] =
        some .semanticIndexNotAllowed := by
  native_decide

/- With `@From` the scope's gates run, one per row: a field, a group that does not repeat, the root
   among them, and a key outside the scope. -/
example :
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Reference"]) =
      some (some .noFieldsAllowed) ∧
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Insured"]) =
      some (some .groupNotRepeatable) ∧
    atRoot (rel ["Claims"] "ClaimRef") [] (.from (.path { base := .absolute, groups := ["Policy"] })) =
      some (some .groupNotRepeatable) ∧
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Payments"]) =
      some (some .entityNotInGroup) := by
  native_decide

/- Without it the placement gates run: keys on parallel paths, a key with no repeatable group below
   the rule group, and a key outside the rule group. Both outsiders read cleanly first, one in a
   repetition iterated jointly with the rule's and one in the repetition holding the rule group,
   so the rule-group gate is theirs. -/
example :
    atRoot (rel ["Claims"] "ClaimRef") [rel ["Payments"] "PayRef"] =
      some (some .notInSamePath) ∧
    atRoot (rel [] "Reference") = some (some .repeatableGroupMissing) ∧
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (key ["Policy", "Payments"] "PayRef") =
      some (some .notInRuleGroup) ∧
    policyVerdict ["Policy", "Claims", "Items"] ["Policy", "Claims", "Items"]
        (key ["Policy", "Claims"] "ClaimRef") =
      some (some .notInRuleGroup) := by
  native_decide

/- Two defects at once: the key list answers ahead of the scope's own gates, and with a scope the
   shared-path check never runs, so parallel keys meet the scope's containment instead. -/
example :
    atRoot (rel [] "Claims") [] (fromGroups ["Insured"]) = some (some .noGroupsAllowed) ∧
    atRoot (rel ["Claims"] "RawNote") [] (fromGroups ["Payments"]) =
      some (some .rawTypeOperandInvalid) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel ["Payments"] "PayRef"] (fromGroups ["Claims"]) =
      some (some .entityNotInGroup) := by
  native_decide

/- The key-list gates answer one gate at a time over the whole list, so the group gate answers ahead
   of the raw one whatever the key order, and the duplicate gate ahead of both: a group named twice
   draws the direct class, and a group beside a key it holds, the root beside any key included, the
   nested one, whichever is written first
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26k-paired-gates)). The peer's duplicate rows
   name the fixed `Insured` and the root; on the repeatable `Claims`, [`kf388`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf388)
   measures a group before its own field, and the group named twice is carried over. -/
example :
    atRoot (rel [] "Insured") [rel ["Claims"] "RawNote"] = some (some .noGroupsAllowed) ∧
    atRoot (rel ["Claims"] "RawNote") [rel [] "Insured"] = some (some .noGroupsAllowed) ∧
    atRoot (rel [] "Insured") [rel [] "Insured"] = some (some .duplicateParam1) ∧
    atRoot (rel [] "Insured") [rel ["Insured"] "InsuredName"] = some (some .duplicateParam2) ∧
    atRoot (key [] "Policy") [rel ["Claims"] "ClaimRef"] = some (some .duplicateParam2) ∧
    atRoot (rel ["Claims"] "ClaimRef") [key [] "Policy"] = some (some .duplicateParam2) ∧
    atRoot (rel [] "Claims") [rel [] "Claims"] = some (some .duplicateParam1) ∧
    atRoot (rel [] "Claims") [rel ["Claims"] "ClaimRef"] = some (some .duplicateParam2) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel [] "Claims"] = some (some .duplicateParam2) := by
  native_decide

/-- The rule at the root reporting on the root's `Reference`, so it iterates nothing. -/
private def atReference (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := [])
    (scope : SurfaceRepetitionNotUniqueScope := .default) :
    Option (Option KernelStaticDiagnostic) :=
  policyVerdict ["Policy"] ["Policy"] first rest scope

/- Every key is read, and walked, before any gate. Reporting at the root, a `Claims` key's read is an
   iteration the rule does not have, and its missing star answers ahead of a group, a raw key and a
   group named twice, written before it or after it. The scope is read as a key is, so a keyed, an
   index-free and an empty repeatable scope draw the same class there. -/
example :
    atReference (rel [] "Reference") [rel ["Claims"] "ClaimRef"] = some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel ["Claims"] "ClaimRef", rel [] "Insured"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel [] "Insured", rel ["Claims"] "ClaimRef"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel ["Claims"] "ClaimRef", rel [] "Memo"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel [] "Memo", rel ["Claims"] "ClaimRef"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel ["Claims"] "ClaimRef", rel [] "Insured", rel [] "Insured"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [rel [] "Insured", rel [] "Insured", rel ["Claims"] "ClaimRef"] =
      some (some .noWildcard) ∧
    atReference (rel [] "Reference") [] (fromGroups ["Claims"]) = some (some .noWildcard) ∧
    atReference (rel [] "Reference") [] (fromGroups ["Notes"]) = some (some .noWildcard) ∧
    atReference (rel [] "Reference") [] (fromGroups ["Vacant"]) = some (some .noWildcard) := by
  native_decide

/- The scope is read with the keys, ahead of the duplicate and raw gates, and its walk answers ahead
   of its emptiness: the rule iterates `Claims`, so the empty repeatable `Vacant`'s level is unbound.
   An index-free `Notes` beside the error field's `Claims` is an unpaired repetition too, and so is a
   second key in it under a scope that holds the first. A key that does not resolve answers ahead of
   the scope; the peer's row reads an index on a group without one, which a plain field path cannot
   spell, so the resolver's miss stands in for it here, read from the same position. -/
example :
    atRoot (rel ["Claims"] "RawNote") [] (fromGroups ["Vacant"]) = some (some .noWildcard) ∧
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Vacant"]) = some (some .noWildcard) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel ["Claims"] "ClaimRef"] (fromGroups ["Vacant"]) =
      some (some .noWildcard) ∧
    atRoot (rel ["Claims"] "Nope") [] (fromGroups ["Vacant"]) = some (some .invalidEntity) ∧
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Notes"]) = some (some .noWildcard) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel ["Notes"] "NoteRef"] (fromGroups ["Claims"]) =
      some (some .noWildcard) := by
  native_decide

/- An outsider in a repetition nothing addresses is refused at its read, ahead of the rule-group
   gate a clean outsider meets. -/
example :
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (rel [] "ClaimRef")
        [key ["Policy", "Notes"] "NoteRef"] =
      some (some .noWildcard) := by
  native_decide

/- The shared-path gate answers ahead of the rule-group gate: from a rule in `Claims`, the jointly
   iterated `Payments` key alone draws the rule-group class and beside a key of `Claims` the
   shared-path one, in either order. An outsider under no repetition at all reads cleanly too, so a
   second key in the fixed `Insured` is the rule-group gate's rather than the repeatable-group one's
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)). -/
example :
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (rel [] "ClaimRef")
        [key ["Policy", "Payments"] "PayRef"] = some (some .notInSamePath) ∧
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (key ["Policy", "Payments"] "PayRef")
        [rel [] "ClaimRef"] = some (some .notInSamePath) ∧
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (rel [] "ClaimRef")
        [key ["Policy", "Insured"] "InsuredName"] = some (some .notInRuleGroup) := by
  native_decide

/-- The rule at the root reporting on its first key's field. -/
private def atFirstKey (writtenGroup : GroupPath) (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath := []) (scope : SurfaceRepetitionNotUniqueScope := .default) :
    Option (Option KernelStaticDiagnostic) :=
  policyVerdict ["Policy"] writtenGroup first rest scope

/- The shared path is the keys' lowest repeatable groups, so keys in the sibling fixed groups
   `Adjuster` and `Assessor` of `Claims` share one, and the Kernel admits them with a scope and
   without one. This theory's topology takes the deepest key's row and refuses two keys whose own
   groups diverge, without a class; so does it a key in the fixed `Claims/Detail` beside one in the
   repeatable `Claims/Items`, which no row reads. Keys in the parallel `Items` and `Parts` of
   `Batches`, jointly iterated on their shared index field, draw the shared-path class without a
   scope, and under one, which asks no shared-path gate, the construct's ban on parallel
   iteration. -/
example :
    atFirstKey ["Policy", "Claims", "Adjuster"] (rel ["Claims", "Adjuster"] "AdjusterRef") = none ∧
    atFirstKey ["Policy", "Claims", "Adjuster"] (rel ["Claims", "Adjuster"] "AdjusterRef")
        [rel ["Claims", "Assessor"] "AssessorRef"] = some none ∧
    atFirstKey ["Policy", "Claims", "Adjuster"] (rel ["Claims", "Adjuster"] "AdjusterRef")
        [rel ["Claims", "Assessor"] "AssessorRef"] (fromGroups ["Claims"]) = some none ∧
    atFirstKey ["Policy", "Claims", "Items"] (rel ["Claims", "Detail"] "DetailRef")
        [rel ["Claims", "Items"] "ItemRef"] = some none ∧
    atFirstKey ["Policy", "Batches", "Items"] (rel ["Batches", "Items"] "ItemRef")
        [rel ["Batches", "Parts"] "PartRef"] = some (some .notInSamePath) ∧
    atFirstKey ["Policy", "Batches", "Items"] (rel ["Batches", "Items"] "ItemRef")
        [rel ["Batches", "Parts"] "PartRef"] (fromGroups ["Batches"]) =
      some (some .parallelIterationNotAllowed) := by
  native_decide

/-- A root `Fleet`, repeatable or not, holding `Plate` and `Vin` directly, `RegNo` in its fixed
    `Registration` and `License` in its repeatable `Drivers`. -/
private def fleetModel (repeatable : Bool) : FlatModel :=
  let scope := if repeatable then [20] else []
  { fields := [
      { id := 1, groupPath := ["Fleet"], name := "Plate", policy := { kind := .string },
        repeatableScope := scope },
      { id := 2, groupPath := ["Fleet"], name := "Vin", policy := { kind := .string },
        repeatableScope := scope },
      { id := 3, groupPath := ["Fleet", "Registration"], name := "RegNo",
        policy := { kind := .string }, repeatableScope := scope },
      { id := 4, groupPath := ["Fleet", "Drivers"], name := "License",
        policy := { kind := .string }, repeatableScope := scope ++ [21] }]
    repeatableGroups :=
      (if repeatable then [{ level := 20, path := ["Fleet"] }] else []) ++
        [{ level := 21, path := ["Fleet", "Drivers"] }] }

/-- The rule at the root `Fleet` reporting on its first key's field. -/
private def fleetVerdict (repeatable : Bool) (writtenGroup : GroupPath) (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath := []) : Option (Option KernelStaticDiagnostic) :=
  match CheckedValidationCondition.fromRepetitionNotUnique (fleetModel repeatable) ["Fleet"]
      { firstKey := first, restKeys := rest } writtenGroup with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => some error.diagnostic?
  | .error _ => some none

/- At a repeatable root, keys all sitting directly in the root skip the repeatable-group gate, and
   the Kernel admits them ([inbound](../../docs/SOURCES.md#inbound-2026-09-26k-paired-gates)). What
   such a rule fires on is unmeasured, and this theory has no reference group to evaluate it against,
   so it refuses them without a class. A key in a fixed subgroup brings the class back, alone or beside
   a direct key, a key in a repeatable subgroup is admitted, and at a fixed root a direct key is the
   measured sole-key shape. -/
example :
    fleetVerdict true ["Fleet"] (rel [] "Plate") = some none ∧
    fleetVerdict true ["Fleet"] (rel [] "Plate") [rel [] "Vin"] = some none ∧
    fleetVerdict true ["Fleet", "Registration"] (rel ["Registration"] "RegNo") =
      some (some .repeatableGroupMissing) ∧
    fleetVerdict true ["Fleet"] (rel [] "Plate") [rel ["Registration"] "RegNo"] =
      some (some .repeatableGroupMissing) ∧
    fleetVerdict true ["Fleet", "Drivers"] (rel ["Drivers"] "License") = none ∧
    fleetVerdict false ["Fleet"] (rel [] "Plate") = some (some .repeatableGroupMissing) := by
  native_decide

/- A rule in `Claims` reporting on the root's `Reference` reads a `Claims` row per row, which the
   walk's containment class refuses, on a key and on a scope alike: the scope is a per-row read too,
   so it does not reach its own containment gate. -/
example :
    policyVerdict ["Policy", "Claims"] ["Policy"] (rel [] "ClaimRef") =
      some (some .fieldNotInRuleGroup) ∧
    policyVerdict ["Policy", "Claims"] ["Policy"] (key ["Policy"] "Reference") []
        (.from (.path { base := .absolute, groups := ["Policy", "Claims"] })) =
      some (some .fieldNotInRuleGroup) := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueDiagnostic
