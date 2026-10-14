import A12Kernel.Elaboration.NumberEntityList

namespace A12Kernel

/-- Group Sum keeps the declaration attached to each reached cell and omitted tail (spec/04). The shared group walk owns scope, capacity and declaration-major ordering for every aggregate. -/
def CheckedNumberEntityGroup.resolvedAggregateSides
    (group : CheckedNumberEntityGroup model) (document : Document) (outer : Env)
    (addressError : StarAddressingError → Error)
    (read : Env → FieldId → Except Error (ValueListCell .number)) :
    Except Error ResolvedNumberEntityAggregateSides := do
  let declarations := (model.groupSubtreeFields group.groupPath).filterMap fun declaration =>
    declaration.toNumberField?.map fun field => (declaration, field.info.signed)
  let rows ← (model.groupOperandRows document outer group.source.boundLevelCount
    declarations (·.1.repeatableScope)).mapError addressError
  let tails ← declarations.filterM fun (declaration, _) =>
    (model.groupOperandUninstantiatedTail document outer group.source.boundLevelCount
      [declaration.repeatableScope]).mapError addressError
  let cells ← readCells rows
  pure {
    values := {
      cells := cells.map (·.cell)
      hasUninstantiatedTail := !tails.isEmpty
      hasHaving := false }
    sum := { cells, uninstantiatedSignedness := tails.map Prod.snd, hasHaving := false } }
where
  readCells : List ((FlatFieldDecl × Bool) × Env) → Except Error (List ResolvedNumericSumCell)
    | [] => pure []
    | ((declaration, signed), environment) :: rest => do
        let cell ← read environment declaration.id
        let entry : ResolvedNumericSumCell := { cell, declarationSigned := signed }
        match cell with
        | .unknown _ => pure [entry]
        | _ => pure (entry :: (← readCells rest))

/-- Only homogeneous slots use operand-level signedness; a group or a selection, whose declarations
may differ in sign, must supply its declaration-aware projection. -/
def CheckedNumberEntityOperand.resolveAggregateSidesWith
    (operand : CheckedNumberEntityOperand model)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number) Terminal))
    (resolveGroup : CheckedNumberEntityGroup model →
      Except Error (Sum ResolvedNumberEntityAggregateSides Terminal))
    (resolveSelected : CheckedSelectedNumberEntity model →
      Except Error (Sum ResolvedNumberEntityAggregateSides Terminal)) :
    Except Error (Sum ResolvedNumberEntityAggregateSides Terminal) := do
  match operand with
  | .group slot => resolveGroup slot
  | .selected source => resolveSelected source
  | _ =>
      match ← resolve operand with
      | .inr result => pure (.inr result)
      | .inl side => pure (.inl {
          values := side, sum := side.toNumericSumSide operand.firstDeclarationSigned })

end A12Kernel
