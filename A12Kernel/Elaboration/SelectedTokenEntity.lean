import A12Kernel.Elaboration.TokenEntityGroup

namespace A12Kernel

/-- Selected tokens retain every declaration's own stored projection; an Enumeration group
cannot borrow its first field's token domain (spec/04 value lists, spec/08 §4.1 selection). -/
structure CheckedSelectedTokenEntity (model : FlatModel) where
  private mk ::
  source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)
  first : CheckedTokenExpansionSlot
  rest : List CheckedTokenExpansionSlot
  allToken : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).all (fun d => d.toStoredTokenSlot?.isSome) = true
  expansionOwned : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).filterMap FlatFieldDecl.toStoredTokenSlot? = first :: rest

namespace CheckedSelectedTokenEntity

def slots (source : CheckedSelectedTokenEntity model) : List CheckedTokenExpansionSlot :=
  source.first :: source.rest

def path (source : CheckedSelectedTokenEntity model) : List String :=
  match source.source with
  | .inl source => source.targetDeclaration.path
  | .inr source => source.entityPath

def isAlreadyMany (source : CheckedSelectedTokenEntity model) : Bool :=
  match source.source with | .inl _ => false | .inr _ => true

def referencesField (source : CheckedSelectedTokenEntity model) (field : FieldId) : Bool :=
  match source.source with
  | .inl source => source.referencesField field
  | .inr source => source.referencesField field

def certify (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except TokenEntityGroupError (CheckedSelectedTokenEntity model) := do
  let declarations := match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations
  let path := match source with
    | .inl source => source.targetDeclaration.path
    | .inr source => source.entityPath
  if allToken : declarations.all (fun d => d.toStoredTokenSlot?.isSome) = true then
    match owned : declarations.filterMap FlatFieldDecl.toStoredTokenSlot? with
    | [] => throw (.expansionEmpty path)
    | first :: rest => pure { source, first, rest, allToken, expansionOwned := owned }
  else throw (.expansionNotToken path)

/-- The index selector supplies phase policy and row identity; token classification remains
owned by each declaration, and the consumer owns stopping and empty-result rules. -/
def sideWith (source : CheckedSelectedTokenEntity model) (phase : Phase)
    (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader) (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide .token) :=
  selectedValueListSideWith (missingStarIsOmitted := missingStarIsOmitted) source.source phase document outer direct stored read column fun declaration value => do
    let some slot := source.slots.find? (·.declaration.id == declaration.id)
      | throw (.checkedDocumentRequired source.path)
    pure (slot.operand.observedValueListCell value)

def sideIn (source : CheckedSelectedTokenEntity model) (phase : Phase)
    (document : CheckedDocument model) (outer : Env) (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide .token) :=
  source.sideWith (missingStarIsOmitted := missingStarIsOmitted) phase document.source.toDocument outer (document.computationContextAt outer).read
    (document.computationContextAt outer).storedText document.computationFillContext.read
    (document.resolveSemanticIndexColumnWith document.read)

def sideAt (source : CheckedSelectedTokenEntity model) (phase : Phase)
    (context : ScalarComputationContext) : Except CheckedAddressingError (ResolvedValueListSide .token) := do
  let some addressed := context.addressed | throw (.checkedDocumentRequired source.path)
  source.sideWith phase addressed.document context.row context.read context.storedText addressed.read
    context.semanticIndexColumnReader

end CheckedSelectedTokenEntity

end A12Kernel
