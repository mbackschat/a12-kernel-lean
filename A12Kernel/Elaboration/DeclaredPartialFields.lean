import A12Kernel.Elaboration.PartialSemanticIndex

namespace A12Kernel

/-- What a missing selection leaves unselected: the absent row of the selected repeatable level, or
the one instance of a root or fixed-group index whose stored key differs
([single-instance key](../../docs/sources/model-structure-and-declaration-probes.md#src-single-instance-key)). -/
inductive DeclaredPartialMissing where
  | row (level : RepeatableLevel)
  | singleInstance

/-- Declared coordinates preserve missing-slot relevance without creating document rows (KF527,
spec/10 §5). Under a missing selection the coordinates serve only the coverage test and must never
be used to read a physical payload: a single instance exists in the document even when its key
differs. -/
structure DeclaredPartialFields where
  addresses : List (FlatFieldDecl × Env)
  missing : Option DeclaredPartialMissing := none

/-- Expand each field's finite declared suffix in declaration-major order. Missing capacity
retains an unsupported extent rather than inventing an iteration limit. -/
def declaredPartialFields? (model : FlatModel) (declarations : List FlatFieldDecl)
    (boundCount : Nat) (outer : Env) :
    Except CheckedAddressingError (Option DeclaredPartialFields) := do
  let mut addresses := []
  for declaration in declarations do
    let some axes := model.repeatableAxesForScope? declaration.repeatableScope
      | throw (.addressing (.unsupportedGroupOperand declaration.groupPath))
    let path : StarPath := { axes, firstStar := boundCount }
    let some rows ← path.declaredEnvironments? outer |>.mapError .addressing | return none
    addresses := addresses ++ rows.map (declaration, ·)
  pure (some { addresses })

/-- Partial selection precedes traversal. An absent parent leaves each lower declared slot
individually subject to wildcard-parent coverage; it does not impose an aggregate extent gate. -/
def resolveDeclaredPartialSelected
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option (CellObservation DeclaredPartialFields)) := do
  let selection := match source with | .inl s => s | .inr s => s.selection.indexSource
  let declarations := match source with | .inl s => [s.targetDeclaration] | .inr s => s.declarations
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  match ← (match source with
    | .inl s => s.selectPartial view outer read
    | .inr s => s.selectPartial view outer read) with
  | none => pure none
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some .empty =>
      let (placeholder, missing) : Env × DeclaredPartialMissing := match selection.group.level? with
        | some level => (outer.filter (fun entry => entry.1 != level) ++ [(level, 1)], .row level)
        | none => (outer, .singleInstance)
      let fields ← declaredPartialFields? model declarations
        selection.indexDeclaration.repeatableScope.length placeholder
      pure (fields.map fun fields => .value { fields with missing := some missing })
  | some (.value row) =>
      pure ((← declaredPartialFields? model declarations
        selection.indexDeclaration.repeatableScope.length row).map CellObservation.value)

/-- Read only a reached relevant slot. Missing selection is empty under parent-wildcard coverage;
otherwise the caller's partial preliminary owns formal and silent unavailability. -/
def DeclaredPartialFields.readCell? (fields : DeclaredPartialFields) (model : FlatModel)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (declaration : FlatFieldDecl) (row : Env) :
    Except CheckedAddressingError (Option CheckedCell) := do
  match fields.missing with
  | some (.row level) =>
      if scope.coversValueListExtent model declaration.path
          (declaration.repeatableScope.filter (· != level)) [level] row then
        pure (some (checkAdmittedRawCell .empty))
      else pure none
  | some .singleInstance =>
      pure (if scope.coversCell model declaration.path row then some (checkAdmittedRawCell .empty) else none)
  | none =>
      if scope.coversCell model declaration.path row then read row declaration.id
      else pure none

end A12Kernel
