import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.EnumerationValueList

/-! # Checked group-scope slots for the String/Enumeration token carrier

A group operand names a field *scope*, so the token family cannot retain it the way it retains a
field-denoting slot. Two facts drive the whole representation here.

The authored surface carries **no read form** on a group slot: `SurfaceFieldEntityOperand.group`
has no `FieldEntityReadForm` where `.field` does. Every expanded declaration is therefore read in
its stored form, and that is a consequence of the syntax rather than a choice about the Kernel.

The projection is nevertheless **per declaration**, not per operand. An Enumeration cell is
classified through its own declaration's resolved projection, so applying the first expanded
declaration's projection to a sibling's cell would silently misread it whenever the two declare
different enumerations. The certified expansion therefore keeps each declaration beside its
operand, and resolution pairs every reached cell with the operand that must read it.

This module owns only the group slot. Slot shape, the star/arity/duplicate gates, and the
whole-list kind and category scans stay with the shared field entity-list checker; the direct and
starred token slots and their runtime stay with the token entity list that imports this one.
-/

namespace A12Kernel

/-- Resolve the exact stored/category token projection selected by a token-family consumer. String supports only the stored/default selection. -/
def FlatFieldDecl.toTokenFieldComparison? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  match projectionRef with
  | .stored => declaration.toTextFieldComparison?
  | .category _ =>
      declaration.toEnumerationTextFieldComparison? projectionRef

/-- One expanded declaration of a group slot beside the operand that reads it. The pair is retained together because the cell classifier needs both: the declaration supplies repeatable scope and identity for addressing, the operand supplies the declaration-owned projection. -/
structure CheckedTokenExpansionSlot where
  declaration : FlatFieldDecl
  operand : FlatTextFieldOperand
  deriving Repr, DecidableEq

/-- Admit one declaration into a group's token expansion, in the stored form a group slot can author. `none` covers every reason the token family cannot read a declaration — a Number or temporal kind, a BOOLEAN or CONFIRM kind, a raw String, an Enumeration without a declaration — and the certificate below turns any such `none` into a refusal of the whole slot rather than a silent omission. -/
def FlatFieldDecl.toStoredTokenSlot? (declaration : FlatFieldDecl) :
    Option CheckedTokenExpansionSlot :=
  (declaration.toTokenFieldComparison? .stored).map fun (operand, _) =>
    { declaration, operand }

/-- One authored group-scope slot certified as String/Enumeration-valued.

    `expansionOwned` and `expansionAllToken` together are the certificate: the retained list **is** the group's recursive subtree in declaration order, nonempty by its shape, and no declaration in that subtree was dropped along the way. The second obligation is what makes the first a completeness claim rather than a filter — without it a subtree of Numbers would certify as an empty selection. -/
structure CheckedTokenEntityGroup (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : CheckedTokenExpansionSlot
  rest : List CheckedTokenExpansionSlot
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toStoredTokenSlot? = first :: rest
  expansionAllToken :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toStoredTokenSlot?.isSome) = true

namespace CheckedTokenEntityGroup

def groupPath (group : CheckedTokenEntityGroup model) : GroupPath :=
  group.source.groupPath

def isStarred (group : CheckedTokenEntityGroup model) : Bool :=
  group.source.isStarred

/-- The certified expansion, in model declaration order. -/
def slots (group : CheckedTokenEntityGroup model) :
    List CheckedTokenExpansionSlot :=
  group.first :: group.rest

/-- Every declared surface kind the slot reaches. A group has no kind of its own, so the consumer that needs one homogeneous kind reads the whole expansion here rather than a single answer that does not exist. -/
def declaredKinds (group : CheckedTokenEntityGroup model) :
    List SurfaceScalarKind :=
  group.slots.map (·.declaration.policy.kind.surfaceKind)

def referencesField (group : CheckedTokenEntityGroup model)
    (field : FieldId) : Bool :=
  group.slots.any (·.declaration.id == field)

end CheckedTokenEntityGroup

/-- Why a group slot is not a token slot. Both arms are deliberately unprojected here: this boundary has no operator, and the class the Kernel reports for a wrong-kind expansion is each operator's own question about the expansion's values. The whole-list kind and category scans in the shared checker are what actually classify a mixed subtree for a consumer that runs them first. -/
inductive TokenEntityGroupError where
  | expansionNotToken (path : List String)
  | expansionEmpty (path : List String)
  deriving Repr, DecidableEq

/-- Certify one authored group slot by expanding it once through the shared subtree query. -/
def certifyTokenEntityGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except TokenEntityGroupError (CheckedTokenEntityGroup model) :=
  if hAll : (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toStoredTokenSlot?.isSome) = true then
    match hOwned :
        (model.groupSubtreeFields source.groupPath).filterMap
          FlatFieldDecl.toStoredTokenSlot? with
    | [] => throw (.expansionEmpty source.groupPath)
    | first :: rest =>
        pure {
          source
          first
          rest
          expansionOwned := hOwned
          expansionAllToken := hAll }
  else
    throw (.expansionNotToken source.groupPath)

namespace CheckedTokenEntityGroup

/-- Read the slot's whole `(row × field)` extent, pairing each reached cell with the operand of the declaration that stored it. The shared group walk owns the extent and its depth; this owns only the projection each cell must be read through. -/
def resolveCheckedValidationCells (group : CheckedTokenEntityGroup model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (List (FlatTextFieldOperand × CheckedAddressedCell)) :=
  document.resolveCheckedGroupEntityOperandPairs outer
    group.source.boundLevelCount
    (group.slots.map fun slot => (slot.declaration, slot.operand))

/-- A token group has complete partial value-list extent only when every declaration in its certified expansion has one covering relevant identifier across the levels the group operand reopens. -/
def partialExtentRelevant (group : CheckedTokenEntityGroup model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  group.slots.all fun slot =>
    scope.coversValueListExtent model slot.declaration.path
      (slot.declaration.repeatableScope.take group.source.boundLevelCount)
      (slot.declaration.repeatableScope.drop group.source.boundLevelCount)
      outer

/-- Resolve the same declaration-paired group extent for partial validation, retaining only relevant concrete cells and recording incomplete extent separately from the cell domain. -/
def resolveCheckedPartialValidationCells
    (group : CheckedTokenEntityGroup model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (List (FlatTextFieldOperand × CheckedAddressedCell) × Bool) := do
  let paired ← document.resolveCheckedGroupEntityOperandPairs outer
    group.source.boundLevelCount
    (group.slots.map fun slot => (slot.declaration, slot))
  let relevant := paired.filter fun pair =>
    scope.coversCell model pair.1.declaration.path pair.2.environment
  pure (relevant.map fun pair => (pair.1.operand, pair.2),
    !group.partialExtentRelevant scope outer)

end CheckedTokenEntityGroup

end A12Kernel
