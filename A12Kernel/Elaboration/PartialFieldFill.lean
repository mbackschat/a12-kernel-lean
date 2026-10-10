import A12Kernel.Elaboration.FieldFillList

namespace A12Kernel

private def declaredFillAddresses (model : FlatModel) (declarations : List FlatFieldDecl)
    (boundCount : Nat) (outer : Env) :
    Except CheckedAddressingError (Option (List (FlatFieldDecl × Env))) := do
  let mut addresses := []
  for declaration in declarations do
    let some axes := model.repeatableAxesForScope? declaration.repeatableScope
      | throw (.addressing (.unsupportedGroupOperand declaration.groupPath))
    let path : StarPath := { axes, firstStar := boundCount }
    let some rows ← path.declaredEnvironments? outer |>.mapError .addressing | return none
    addresses := addresses ++ rows.map (declaration, ·)
  pure (some addresses)

private def unavailableFill : ValidationFillTally :=
  { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }

private def emptyFill : ValidationFillTally :=
  { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }

private def partialFillAddresses (model : FlatModel) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (addresses : List (FlatFieldDecl × Env)) : Except CheckedAddressingError ValidationFillTally :=
  addresses.foldlM (fun tally (declaration, row) => do
    if !scope.coversCell model declaration.path row then return tally.combine unavailableFill
    let some cell ← read row declaration.id | return tally.combine unavailableFill
    pure (tally.combine (observeCell .validation cell).asValidationFillTally)) emptyFill

/-- KF527's missing selected parent has no payload to read. Each descendant slot is empty only
under coverage wildcarding that parent; concrete child identifiers may cover it (spec/10 §5).
Keeping the per-slot classifications lets existential and universal quantifiers differ. -/
private def partialSelectedFill
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError ValidationFillTally := do
  let selection := match source with | .inl s => s | .inr s => s.selection.indexSource
  let declarations := match source with | .inl s => [s.targetDeclaration] | .inr s => s.declarations
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  match ← selection.selectPartial view outer read with
  | none | some (.unknown _) | some (.poison _) => pure unavailableFill
  | some .empty =>
      let selectedLevel := selection.group.level
      let placeholder := outer.filter (fun entry => entry.1 != selectedLevel) ++ [(selectedLevel, 1)]
      let some addresses ← declaredFillAddresses model declarations
          selection.indexDeclaration.repeatableScope.length placeholder | return unavailableFill
      pure (addresses.foldl (fun tally (declaration, row) => tally.combine
        (if scope.coversValueListExtent model declaration.path
            (declaration.repeatableScope.filter (· != selectedLevel)) [selectedLevel] row then
          { emptyFill with empty := 1 }
        else unavailableFill)) emptyFill)
  | some (.value row) =>
      let some addresses ← declaredFillAddresses model declarations
          selection.indexDeclaration.repeatableScope.length row | return unavailableFill
      partialFillAddresses model scope read addresses

private def CheckedFieldFillOperand.partialFillTally (operand : CheckedFieldFillOperand model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError ValidationFillTally := do
  match operand with
  | .indexed source => partialSelectedFill (.inl source) document scope outer read
  | .keyed source => partialSelectedFill (.inr source) document scope outer read
  | .field declaration => partialFillAddresses model scope read [(declaration, outer)]
  | .star source =>
      let some rows ← source.source.path.declaredEnvironments? outer |>.mapError .addressing
        | return unavailableFill
      partialFillAddresses model scope read (rows.map (source.source.declaration, ·))
  | .group source =>
      let some addresses ← declaredFillAddresses model source.declarations source.source.boundLevelCount outer
        | return unavailableFill
      partialFillAddresses model scope read addresses

/-- Unfiltered partial fill retains each declared slot's relevance, including missing rows.
The seven quantifiers share the existing tally laws: unavailable cells neither witness presence
nor absence, but do prevent a universal conclusion (KF527, spec/10 §5). The supplied call-local
reader preserves silent preliminary unavailability; no document row is materialized. -/
def CheckedFieldFillList.evaluatePartialFill (list : CheckedFieldFillList model)
    (operator : FieldFillQuantifier) (document : CheckedDocument model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError Verdict := do
  if list.hasHaving then return .unknown
  let tally ← list.operands.foldlM (fun tally operand => do
    pure (tally.combine (← operand.partialFillTally document scope outer read))) emptyFill
  pure (operator.evalValidation tally).asConservativeVerdict

end A12Kernel
