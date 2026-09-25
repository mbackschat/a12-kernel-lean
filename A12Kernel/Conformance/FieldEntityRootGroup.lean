import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TokenEntityValueList

/-! # A12Kernel.Conformance.FieldEntityRootGroup — the shared entity list's root-group gate

A root group is refused as an entity-list operand with `MVK_ROOT_GROUP_REFERENCED`, and the gate is
asked of the list the duplicate scans return rather than of each operand as it is read. Two
consequences separate it from a per-operand refusal, and the cases below lock both on two carriers
the Kernel measures it on, `FirstFilledValue` and the Number `FieldValuesNotUnique`
([inbound](../../docs/SOURCES.md#inbound-2026-09-23-entity-list-root-group-gate)), plus the
value-list quantifier's root rows:

* every entity of a model lies under its root, so a root beside any entity of its **own** root is a
  nested duplicate and the root gate never speaks there;
* only a model with a **second** root can hold a root beside something not under it, and there the
  root gate answers ahead of the carrier's own kind gates.

The fixture therefore carries four roots: `Item` is mixed, `Extra` holds a single String, and
`Totals` holds only Numbers, so a missing gate shows up as an **admitted** list on the last two
rather than as some other refusal, and `Ledger` holds only a Date, which the value list's kind gate
refuses. `Item/Handling` is the non-root fixed group every admitted group control reads. `Item/Lapses` is an empty repeatable group, the one unreadable
operand this representation can build, and the last section locks that an operand's own read
refusal precedes every list gate here, the root gate included.
-/

namespace A12Kernel.Conformance.FieldEntityRootGroup

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def rootsModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Item"], name := "Title",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Item"], name := "Weight",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Item"], name := "InStock",
        policy := { kind := .confirm } },
      { id := 4, groupPath := ["Extra"], name := "Code",
        policy := { kind := .string } },
      { id := 5, groupPath := ["Totals"], name := "Net",
        policy := { kind := .number unsigned } },
      { id := 6, groupPath := ["Totals"], name := "Gross",
        policy := { kind := .number unsigned } },
      { id := 7, groupPath := ["Ledger"], name := "Booked",
        policy := { kind := .temporal .date TemporalComponents.fullDate } },
      { id := 8, groupPath := ["Item", "Handling"], name := "Label",
        policy := { kind := .string } }]
    repeatableGroups := [{ level := 10, path := ["Item", "Lapses"], repeatability := some 3 }] }

private def group (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def field (groups : List String) (name : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field := name }

private inductive Decision where
  | admitted
  | mapped (diagnostic : KernelStaticDiagnostic)
  | rejectedUnmapped
  deriving Repr, DecidableEq

private def firstFilled (operands : List SurfaceFieldEntityOperand) : Option Decision :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateFirstFilledTokenSource rootsModel ["Item"] { first, rest } with
      | .ok _ => some .admitted
      | .error error =>
          some (match error.diagnostic? with
            | some diagnostic => .mapped diagnostic
            | none => .rejectedUnmapped)

private def numberNotUnique (operands : List SurfaceFieldEntityOperand) : Option Decision :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource rootsModel ["Item"] { first, rest } with
      | .ok _ => some .admitted
      | .error error =>
          some (match error.diagnostic? with
            | some diagnostic => .mapped diagnostic
            | none => .rejectedUnmapped)

/-! ## A lone root is refused whatever it holds

`Extra` and `Totals` are each homogeneous for their carrier, so without the gate both lists would be
admitted; `Item` would reach a kind refusal instead. -/

example :
    firstFilled [group ["Extra"]] = some (.mapped .rootGroupReferenced) ∧
    firstFilled [group ["Item"]] = some (.mapped .rootGroupReferenced) ∧
    numberNotUnique [group ["Totals"]] = some (.mapped .rootGroupReferenced) := by
  native_decide

/-! ## The duplicate scans answer first

A root repeated is the exact duplicate, and a root beside an entity of its own root is the nested
one, in either authored order. -/

example :
    firstFilled [group ["Item"], group ["Item"]] = some (.mapped .duplicateParam1) ∧
    firstFilled [group ["Item"], field ["Item"] "Title"] =
      some (.mapped .duplicateParam2) ∧
    firstFilled [field ["Item"] "Title", group ["Item"]] =
      some (.mapped .duplicateParam2) ∧
    numberNotUnique [group ["Totals"], field ["Totals"] "Net"] =
      some (.mapped .duplicateParam2) := by
  native_decide

/-! ## Beside another root's entity, the root answers ahead of the kind gates

`Extra` beside `Title` is homogeneous String, so the gate alone refuses it; beside `Weight` the same
root outranks the String/Number mix. The two direct fields from different roots are the admitted
control, which is what shows the refusal belongs to the root operand and not to the second root. -/

example :
    firstFilled [group ["Extra"], field ["Item"] "Title"] =
      some (.mapped .rootGroupReferenced) ∧
    firstFilled [group ["Extra"], field ["Item"] "Weight"] =
      some (.mapped .rootGroupReferenced) ∧
    firstFilled [group ["Item"], field ["Extra"] "Code"] =
      some (.mapped .rootGroupReferenced) ∧
    firstFilled [field ["Item"] "Title", field ["Extra"] "Code"] = some .admitted := by
  native_decide

private def shapeError? (operands : List SurfaceFieldEntityOperand) :
    Option FieldEntityShapeElabError :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateFieldEntityShape rootsModel ["Item"] (writtenGroup := ["Item"]) { first, rest } with
      | .error error => some error
      | .ok _ => none

/- The shared shape names the root it refused, so the class above is the list gate's and not a
   carrier's own. -/
example :
    shapeError? [field ["Item"] "Title", group ["Extra"]] =
      some (.rootGroupOperand ["Extra"]) := by
  native_decide

/- The value-list quantifier reaches the same gate through the same shape, with a root alone as well
   as beside another root's field, where two direct fields from different roots are admitted
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)). -/
private def valueList (operands : List SurfaceFieldEntityOperand)
    (quantifier : ValueListQuantifier := .atLeastOne) : Option Decision :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateTokenEntityStringLiteralValueListSource rootsModel ["Item"]
          { quantifier, fields := { first, rest }, values := ["x"] } with
      | .ok _ => some .admitted
      | .error error =>
          some (match error.diagnostic? with
            | some diagnostic => .mapped diagnostic
            | none => .rejectedUnmapped)

example :
    valueList [group ["Extra"]] = some (.mapped .rootGroupReferenced) ∧
    valueList [group ["Extra"], field ["Item"] "Title"] = some (.mapped .rootGroupReferenced) ∧
    valueList [field ["Extra"] "Code", field ["Item"] "Title"] = some .admitted := by
  native_decide

private def quantifiers : List ValueListQuantifier := [.atLeastOne, .no, .notAll]

/- The peer's value-list rows, read at a12-dmkits `40f6d53c4`
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-dispositions)). All three quantifiers share
   the gate and its order: the duplicate scan answers ahead of it, and it answers ahead of the kind
   gate, where `Ledger` draws the root class and its Date alone the kind class. -/
example :
    quantifiers.all (fun quantifier =>
      valueList [group ["Extra"]] quantifier == some (.mapped .rootGroupReferenced) &&
      valueList [group ["Extra"], field ["Item"] "Title"] quantifier ==
        some (.mapped .rootGroupReferenced) &&
      valueList [group ["Item"], field ["Item"] "Title"] quantifier ==
        some (.mapped .duplicateParam2) &&
      valueList [group ["Ledger"]] quantifier == some (.mapped .rootGroupReferenced) &&
      valueList [field ["Ledger"] "Booked"] quantifier ==
        some (.mapped .onlyStringEnumNumberAllowed)) = true := by
  native_decide

private def entityValueList (fields values : SurfaceFieldEntityOperand)
    (quantifier : ValueListQuantifier := .atLeastOne) : Option Decision :=
  match elaborateTokenEntityValueListSource rootsModel ["Item"]
      { quantifier, fields := { first := fields, rest := [] },
        values := { first := values, rest := [] } } with
  | .ok _ => some .admitted
  | .error error =>
      some (match error.diagnostic? with
        | some diagnostic => .mapped diagnostic
        | none => .rejectedUnmapped)

/- In the field-read spelling a root on either side draws the root class, and so does a root across
   the `In` from its own field, which one list would report as the nested duplicate. Two fields from
   different roots are the admitted control. -/
example :
    entityValueList (group ["Extra"]) (field ["Item"] "Title") =
      some (.mapped .rootGroupReferenced) ∧
    entityValueList (field ["Item"] "Title") (group ["Extra"]) =
      some (.mapped .rootGroupReferenced) ∧
    entityValueList (group ["Item"]) (field ["Item"] "Title") =
      some (.mapped .rootGroupReferenced) ∧
    entityValueList (field ["Item"] "Title") (group ["Item"]) =
      some (.mapped .rootGroupReferenced) ∧
    entityValueList (field ["Extra"] "Code") (field ["Item"] "Title") = some .admitted := by
  native_decide

/- The peer's remaining value-list rows, on all three quantifiers: a non-root fixed group is
   admitted alone and beside another root's field in the literal spelling and on either side of the
   `In`, while a root across the `In` from another root's field draws the root class in either
   direction, and the field-read rows above hold on `No` and `NotAll` too. -/
example :
    let handling := group ["Item", "Handling"]
    let code := field ["Extra"] "Code"
    quantifiers.all (fun quantifier =>
      valueList [handling] quantifier == some .admitted &&
      valueList [handling, code] quantifier == some .admitted &&
      entityValueList handling code quantifier == some .admitted &&
      entityValueList code handling quantifier == some .admitted &&
      entityValueList (group ["Ledger"]) code quantifier == some (.mapped .rootGroupReferenced) &&
      entityValueList code (group ["Ledger"]) quantifier == some (.mapped .rootGroupReferenced) &&
      entityValueList (group ["Extra"]) (field ["Item"] "Title") quantifier ==
        some (.mapped .rootGroupReferenced) &&
      entityValueList (field ["Item"] "Title") (group ["Item"]) quantifier ==
        some (.mapped .rootGroupReferenced) &&
      entityValueList code (field ["Item"] "Title") quantifier == some .admitted) = true := by
  native_decide

/- A field name that does not resolve is the shared resolver's refusal carried through the same
   shape, so an unknown root segment and an unknown name below a known root keep their two classes
   on every entity-list carrier; `FirstFilledValue` is the one measured with the resolver batch
   ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)). -/
example :
    firstFilled [field ["Nope"] "Title", field ["Item"] "Title"] =
      some (.mapped .invalidRootGroup) ∧
    firstFilled [field ["Item"] "Nope", field ["Item"] "Title"] =
      some (.mapped .invalidEntity) := by
  native_decide

/- A group or starred group operand that does not resolve carries the same split through the shape.
   No entity-list row separates a group miss from a field miss, since the Kernel reads the same
   spelling either way; the classes are the group carriers'
   ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)). -/
private def missingStar : SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups := [{ name := "Item" }, { name := "Nope", starred := true }] }

example :
    firstFilled [group ["Nope", "Lapses"], field ["Item"] "Title"] =
      some (.mapped .invalidRootGroup) ∧
    firstFilled [group ["Item", "Nope"], field ["Item"] "Title"] =
      some (.mapped .invalidEntity) ∧
    firstFilled [missingStar, field ["Item"] "Title"] = some (.mapped .invalidEntity) := by
  native_decide

/-! ## An operand's own read refusal precedes every list gate

The empty starred group is refused while it is resolved, and every operand is resolved before the
duplicate scans, so it answers leading a repeated field, trailing one, and beside the root that
contains it — the Kernel's `Lapses*` and `Sum(/Item, Hollow)` rows
([inbound](../../docs/SOURCES.md#inbound-2026-09-23b-entity-list-operand-reads)). The shape error
names the group, and both carriers project it to `MVK_GROUP_IS_EMPTY`. -/

private def lapses : SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups := [{ name := "Item" }, { name := "Lapses", starred := true }] }

example :
    let empty := some (.starredGroup (.groupHasNoFields ["Item", "Lapses"]))
    shapeError? [lapses, field ["Item"] "Title", field ["Item"] "Title"] = empty ∧
    shapeError? [field ["Item"] "Title", field ["Item"] "Title", lapses] = empty ∧
    shapeError? [group ["Item"], lapses] = empty := by
  native_decide

example :
    firstFilled [lapses, field ["Item"] "Title", field ["Item"] "Title"] =
      some (.mapped .groupIsEmpty) ∧
    firstFilled [field ["Item"] "Title", field ["Item"] "Title", lapses] =
      some (.mapped .groupIsEmpty) ∧
    firstFilled [group ["Item"], lapses] = some (.mapped .groupIsEmpty) ∧
    numberNotUnique [lapses] = some (.mapped .groupIsEmpty) ∧
    numberNotUnique [field ["Item"] "Weight", lapses] = some (.mapped .groupIsEmpty) := by
  native_decide

/- `RuleGroup` in a rule declared at the empty group is the one spelling the shape lets through, so
   each carrier's own empty-expansion refusal is reachable only that way. It stays unmapped because
   no row measures it: the measurement instrument refuses a rule declared there before the Kernel
   sees it ([SG9](../../docs/gaps/paths-and-groups.md#gap-sg9)). -/
example :
    (elaborateFieldEntityShape rootsModel ["Item", "Lapses"] (writtenGroup := ["Item", "Lapses"])
      { first := .group (.ruleGroup false), rest := [] }).toOption.isSome = true := by
  native_decide

end A12Kernel.Conformance.FieldEntityRootGroup
