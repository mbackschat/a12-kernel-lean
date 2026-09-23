import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenFirstFilledValue

/-! # A12Kernel.Conformance.FieldEntityRootGroup — the shared entity list's root-group gate

A root group is refused as an entity-list operand with `MVK_ROOT_GROUP_REFERENCED`, and the gate is
asked of the list the duplicate scans return rather than of each operand as it is read. Two
consequences separate it from a per-operand refusal, and the cases below lock both on two carriers
the Kernel measures it on, `FirstFilledValue` and the Number `FieldValuesNotUnique`
([inbound](../../docs/SOURCES.md#inbound-2026-09-23-entity-list-root-group-gate)):

* every entity of a model lies under its root, so a root beside any entity of its **own** root is a
  nested duplicate and the root gate never speaks there;
* only a model with a **second** root can hold a root beside something not under it, and there the
  root gate answers ahead of the carrier's own kind gates.

The fixture therefore carries three roots: `Item` is mixed, `Extra` holds a single String, and
`Totals` holds only Numbers, so a missing gate shows up as an **admitted** list on the last two
rather than as some other refusal. `Item/Lapses` is an empty repeatable group, the one unreadable
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
        policy := { kind := .number unsigned } }]
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
      match elaborateFieldEntityShape rootsModel ["Item"] { first, rest } with
      | .error error => some error
      | .ok _ => none

/- The shared shape names the root it refused, so the class above is the list gate's and not a
   carrier's own. -/
example :
    shapeError? [field ["Item"] "Title", group ["Extra"]] =
      some (.rootGroupOperand ["Extra"]) := by
  native_decide

/-! ## An operand's own read refusal precedes every list gate

The empty starred group is refused while it is resolved, and every operand is resolved before the
duplicate scans, so it answers leading a repeated field, trailing one, and beside the root that
contains it — the Kernel's `Lapses*` and `Sum(/Item, Hollow)` rows
([inbound](../../docs/SOURCES.md#inbound-2026-09-23b-entity-list-operand-reads)). The shared
projection names no class for that refusal ([SG9](../../docs/gaps/paths-and-groups.md#gap-sg9)), so
the shape error is what these lock. -/

private def lapses : SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups := [{ name := "Item" }, { name := "Lapses", starred := true }] }

example :
    let empty := some (.starredGroup (.groupHasNoFields ["Item", "Lapses"]))
    shapeError? [lapses, field ["Item"] "Title", field ["Item"] "Title"] = empty ∧
    shapeError? [field ["Item"] "Title", field ["Item"] "Title", lapses] = empty ∧
    shapeError? [group ["Item"], lapses] = empty := by
  native_decide

end A12Kernel.Conformance.FieldEntityRootGroup
