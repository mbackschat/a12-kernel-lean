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
      { id := 8, groupPath := ["Policy", "Payments"], name := "ClaimRef",
        policy := { kind := .string }, repeatableScope := [11] },
      { id := 9, groupPath := ["Policy", "Payments"], name := "PayRef",
        policy := { kind := .string }, repeatableScope := [11] },
      { id := 10, groupPath := ["Policy", "Notes"], name := "NoteRef",
        policy := { kind := .string }, repeatableScope := [13] },
      { id := 11, groupPath := ["Policy", "Claims", "Detail"], name := "DetailRef",
        policy := { kind := .string }, repeatableScope := [10] }]
    repeatableGroups := [
      { level := 10, path := ["Policy", "Claims"], indexField := some 4 },
      { level := 12, path := ["Policy", "Claims", "Items"] },
      { level := 11, path := ["Policy", "Payments"], indexField := some 8 },
      { level := 13, path := ["Policy", "Notes"] },
      { level := 14, path := ["Policy", "Vacant"] }] }

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

/- A semantic index on a key is refused whichever field the rule reports on: here the key is
   `Amount` and the error field `ClaimRef`. -/
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

/- Two defects at once: the key list answers ahead of the scope, and with a scope the shared-path
   check never runs, so parallel keys meet the scope's containment instead. -/
example :
    atRoot (rel [] "Claims") [] (fromGroups ["Insured"]) = some (some .noGroupsAllowed) ∧
    atRoot (rel ["Claims"] "RawNote") [] (fromGroups ["Payments"]) =
      some (some .rawTypeOperandInvalid) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel ["Payments"] "PayRef"] (fromGroups ["Claims"]) =
      some (some .entityNotInGroup) := by
  native_decide

/- The list's duplicate gate answers ahead of the group gate: a group named twice draws the direct
   class, and a group beside a key it holds, the root beside any key included, the nested one,
   whichever is written first. On this carrier `kf388` measures a group before its own field and the
   `-26f` letter a starred field before its group; a group named twice and the root beside a key are
   measured on the other list carriers sharing the list builder
   ([`kf388`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf388)), an assumption SG9 records. -/
example :
    atRoot (rel [] "Claims") [rel [] "Claims"] = some (some .duplicateParam1) ∧
    atRoot (rel [] "Claims") [rel ["Claims"] "ClaimRef"] = some (some .duplicateParam2) ∧
    atRoot (rel ["Claims"] "ClaimRef") [rel [] "Claims"] = some (some .duplicateParam2) ∧
    atRoot (key [] "Policy") [rel ["Claims"] "ClaimRef"] = some (some .duplicateParam2) := by
  native_decide

/- The scope is read as a key is. An index-free `Notes` beside the error field's `Claims` is an
   unpaired repetition, and a scope below a root error field is one the rule does not iterate, so
   both draw the walk's missing-star class rather than containment, as the peer measured on its
   index-free carrier; this `Claims` is keyed, an assumption SG9 records. So does a second key in
   `Notes` under a scope that holds the first. -/
example :
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Notes"]) = some (some .noWildcard) ∧
    policyVerdict ["Policy"] ["Policy"] (rel [] "Reference") [] (fromGroups ["Claims"]) =
      some (some .noWildcard) ∧
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

/- An empty scope is refused ahead of containment, but without a class. The peer's row, drawing the
   empty-group class, names an empty fixed group, which this model cannot build
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26h-empty-scope)); the empty repeatable `Vacant`
   also meets the walk, and no row fixes which of the two answers first. -/
example :
    atRoot (rel ["Claims"] "ClaimRef") [] (fromGroups ["Vacant"]) = some none := by
  native_decide

/- The shared-path gate compares the keys' lowest repeatable groups, so a key in the fixed
   `Claims/Detail` lies on one path with a key in `Claims/Items`; the two own groups still diverge,
   which this theory's topology refuses without a class. -/
example :
    policyVerdict ["Policy"] ["Policy", "Claims", "Items"] (rel ["Claims", "Detail"] "DetailRef")
        [rel ["Claims", "Items"] "ItemRef"] =
      some none := by
  native_decide

/- An outsider under no repetition at all reads cleanly too: beside a rule in `Claims`, a second key
   in the fixed `Insured` is the rule-group gate's rather than the repeatable-group one's, as the peer
   measured on a second key in a fixed sibling of the rule's repeatable group
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)). -/
example :
    policyVerdict ["Policy", "Claims"] ["Policy", "Claims"] (rel [] "ClaimRef")
        [key ["Policy", "Insured"] "InsuredName"] =
      some (some .notInRuleGroup) := by
  native_decide

/-- A root `Ledger` holding `Key` directly and `Entry` in its fixed `Detail`, repeatable or not. -/
private def ledgerModel (repeatable : Bool) : FlatModel :=
  let scope := if repeatable then [20] else []
  { fields := [
      { id := 1, groupPath := ["Ledger"], name := "Key", policy := { kind := .string },
        repeatableScope := scope },
      { id := 2, groupPath := ["Ledger", "Detail"], name := "Entry", policy := { kind := .string },
        repeatableScope := scope }]
    repeatableGroups := if repeatable then [{ level := 20, path := ["Ledger"] }] else [] }

private def ledgerVerdict (repeatable : Bool) (first : SurfaceFieldPath) :
    Option (Option KernelStaticDiagnostic) :=
  match CheckedValidationCondition.fromRepetitionNotUnique (ledgerModel repeatable) ["Ledger"]
      { firstKey := first, restKeys := [] } ["Ledger"] with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => some error.diagnostic?
  | .error _ => some none

/- A rule at a repeatable root whose keys all sit directly in a root group skips the Kernel's
   repeatable-group gate, a source reading no row measures, so the shape claims no class. A fixed root
   is the measured sole-key shape, and a key one group deeper is outside the exemption. -/
example :
    ledgerVerdict true (rel [] "Key") = some none ∧
    ledgerVerdict false (rel [] "Key") = some (some .repeatableGroupMissing) ∧
    ledgerVerdict true (rel ["Detail"] "Entry") = some (some .repeatableGroupMissing) := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueDiagnostic
