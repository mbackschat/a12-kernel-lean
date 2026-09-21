import A12Kernel.Elaboration.Flat.Model

/-! # A12Kernel.Conformance.ModelDeclarationLegality — declaration-admission locks

Two Kernel laws that gate a model before any condition is read: the one whole name A12 reserves, and the repeatability ceiling, which depends on the declaring carrier rather than on one global bound.

These are admission locks over `FlatModel.validate`. They say nothing about how a repeatable group evaluates, and nothing about the reader tier below A12's own verdicts — a count past a signed 32-bit integer is not read at all, which `Nat` cannot express and which no clause here claims.
-/

namespace A12Kernel.Conformance.ModelDeclarationLegality

open A12Kernel

private def namedField (path : GroupPath) (name : String) : FlatFieldDecl :=
  { id := 1, groupPath := path, name, policy := { kind := .string },
    repeatableScope := [] }

private def scalarField (path : GroupPath) : FlatFieldDecl := namedField path "A"

private def rootedModel (root : String) : FlatModel :=
  { fields := [scalarField [root]] }

private def admits (model : FlatModel) : Bool := model.validate.isOk

/-- **`Id` is the one whole name A12 refuses, and only as the root group's.** The match is the
entire name rather than a prefix or an alphabet rule, so `Identity` and `BinId` stay admitted and
only the four spellings of the reserved word are refused; a name is not an alphabet
([`kf367`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf367)). -/
example :
    admits (rootedModel "Bin") = true ∧
      ["Id", "ID", "id", "iD"].all (fun name => admits (rootedModel name)) = false ∧
      ["Identity", "BinId", "Idx"].all (fun name => admits (rootedModel name)) = true := by
  native_decide

/-- The reservation is the **root carrier's** law. The same name one level down, and on a field,
is ordinary. Without these rows the case above would also be satisfied by a model-wide ban. -/
example :
    admits { fields := [scalarField ["Bin", "Id"]] } = true ∧
      admits { fields := [namedField ["Bin"] "Id"] } = true := by
  native_decide

private def cappedModel (path : GroupPath) (maximum : Nat) : FlatModel :=
  { fields := [{ id := 1, groupPath := path, name := "A", policy := { kind := .string }, repeatableScope := [10] }],
    repeatableGroups := [{ level := 10, path, repeatability := some maximum }] }

private def rootCapped (maximum : Nat) : FlatModel := cappedModel ["Rows"] maximum
private def nestedCapped (maximum : Nat) : FlatModel := cappedModel ["Src", "Rows"] maximum

/-- **The repeatability ceiling depends on the carrier, and the two bounds are an order of magnitude
apart.** A root group admits up to `999999999` and a nested one up to `1999999999`; each refuses at
the next count ([`kf365`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf365)). Both carriers are
walked rather than one measured and the other inherited, because a single bound would either refuse
a legal nested group or accept an illegal root one — the two middle rows are exactly that separator. -/
example :
    admits (rootCapped 999999999) = true ∧
      admits (rootCapped 1000000000) = false ∧
      admits (nestedCapped 1000000000) = true ∧
      admits (nestedCapped 1999999999) = true ∧
      admits (nestedCapped 2000000000) = false := by
  native_decide

/-- An omitted maximum is a group that repeats once, not an unbounded one, so it clears a gate that
no count could clear by being absent. `1` is the smallest legal declaration and stays admitted. -/
example :
    admits { fields := (nestedCapped 1).fields, repeatableGroups := [{ level := 10, path := ["Src", "Rows"] }] } = true ∧
      admits (nestedCapped 1) = true := by
  native_decide

end A12Kernel.Conformance.ModelDeclarationLegality
