import A12Kernel.Elaboration.TemporalExpression.DateComponents
import A12Kernel.Elaboration.TemporalExpression.EntityList

namespace A12Kernel

mutual
private def scalarTemporalDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α) (expression : ScalarTemporalExpression model) : List α :=
  match expression with
  | .atom source => scalarTemporalAtomDependencies storedOnly field entity indexed numeric source
  | .apply operation first rest =>
      scalarTemporalDependencies storedOnly field entity indexed numeric first ++
        (rest.attach.flatMap fun ⟨source, _⟩ => scalarTemporalDependencies storedOnly field entity indexed numeric source) ++
        scalarTemporalOperationDependencies storedOnly field entity indexed numeric operation
termination_by sizeOf expression

private def scalarTemporalAtomDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α) (atom : ScalarTemporalAtom model) : List α :=
  match atom with
  | .dateConstruction components =>
      components.attach.sources.flatMap fun ⟨component, _⟩ =>
        scalarDateComponentDependencies storedOnly field entity indexed numeric component
  | .valueAsDate source => field source.source.target.id
  | .indexedValueAsDate source =>
      (if storedOnly then field source.selection.targetDeclaration.id else []) ++ indexed source.selection
  | .timeConstruction components => scalarTemporalComponentDependencies storedOnly field entity indexed numeric components
  | .field source => if storedOnly then [] else field source.id
  | .indexed source => indexed source
  | .entityExtremum _ source => if storedOnly then [] else entity source
  | .rangeBound _ (.exact source) => if storedOnly then [] else field source.source.id
  | .rangeBound _ (.yearless source) => if storedOnly then [] else field source.source.id
  | _ => []
termination_by sizeOf atom

private def scalarDateComponentDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α) (component : ScalarDateComponent model) : List α :=
  match component with
  | .inl (.inl source) =>
      if storedOnly then
        match source with
        | .dateYearField source => field source.source.id
        | _ => []
      else source.fieldId?.toList.flatMap field
  | .inl (.inr source) =>
      (if storedOnly then field source.selection.targetDeclaration.id else []) ++ indexed source.selection
  | .inr source => scalarTemporalNumericDependencies storedOnly field entity indexed numeric source
termination_by sizeOf component

private def scalarTemporalOperationDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α) (operation : ScalarTemporalTransform model) : List α :=
  match operation with
  | .subdayShift _ _ amount | .calendarShift _ _ amount =>
      match amount.mapMSubterm (fun atom _ => (Except.ok (scalarTemporalNumericDependencies storedOnly field entity indexed numeric atom) : Except Empty (List α))) with
      | .ok result => result.atoms.flatten
      | .error error => nomatch error
  | _ => []
termination_by sizeOf operation

private def scalarTemporalNumericDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α) (atom : ScalarTemporalNumericAtom model) : List α :=
  match atom with
  | .numeric source => numeric source ++ source.flatMapTemporalSubterm fun child _ =>
      scalarTemporalDependencies storedOnly field entity indexed numeric child
  | .indexedPart selection _ _ => indexed selection
  | .ordinary source => if storedOnly then [] else source.fieldDependencies.flatMap field
  | .projection _ _ source => scalarTemporalDependencies storedOnly field entity indexed numeric source
termination_by sizeOf atom
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)

private def scalarTemporalComponentDependency (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α)
    (component : ScalarTimeComponent model) : List α :=
  match component with
  | .inl (.inl source) => if storedOnly then [] else source.fieldDependencies.flatMap field
  | .inl (.inr source) => indexed source.selection
  | .inr source => scalarTemporalNumericDependencies storedOnly field entity indexed numeric source
termination_by sizeOf component

private def scalarTemporalComponentDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α)
    (components : TimeComponentPrefix (ScalarTimeComponent model)) : List α :=
  match components with
  | .empty => []
  | .hour hour => scalarTemporalComponentDependency storedOnly field entity indexed numeric hour
  | .minute hour minute => scalarTemporalComponentDependency storedOnly field entity indexed numeric hour ++ scalarTemporalComponentDependency storedOnly field entity indexed numeric minute
  | .second hour minute second => scalarTemporalComponentDependency storedOnly field entity indexed numeric hour ++
      scalarTemporalComponentDependency storedOnly field entity indexed numeric minute ++ scalarTemporalComponentDependency storedOnly field entity indexed numeric second
termination_by sizeOf components
end

namespace ScalarTemporalExpression

/-- Reuse the complete recursive dependency traversal with consumer-owned projections of each retained source shape. -/
def dependenciesWith (expression : ScalarTemporalExpression model)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α :=
      fun atom => (atom.fieldOriginsWith (fun _ => [])).flatMap (field ∘ Prod.snd)) : List α :=
  scalarTemporalDependencies false field entity indexed numeric expression

def hasHaving (expression : ScalarTemporalExpression model) : Bool :=
  !(scalarTemporalDependencies false (fun _ => ([] : List Unit))
    (fun source => if source.filters.any Option.isSome then [()] else []) (fun _ => []) (fun _ => []) expression).isEmpty

/-- Stored-text requirements include recursively nested temporal operands. -/
def storedTextFields (expression : ScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies true (fun field => [field]) (·.fieldIds)
    (fun source => match source.key with | .field key => [key.id] | .literal .. => []) (fun _ => []) expression

def fieldIds (expression : ScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies false (fun field => [field]) (·.fieldIds)
    (fun source => (model.fields.filter fun field => source.referencesField field.id).map (·.id))
    (fun atom => atom.fieldOriginsWith (fun _ => []) |>.map Prod.snd) expression

/-- Selected targets remain scheduler inputs while index and star selection bind their own rows (spec/08 §4). -/
def bindingScopes (expression : ScalarTemporalExpression model) : List (List RepeatableLevel) :=
  scalarTemporalDependencies false
    (fun field => ((model.lookupUniqueId field).toOption.map (·.repeatableScope)).toList)
    (·.bindingScopes)
    (·.bindingScopes)
    (fun atom => match atom with
      | .repetition reference => (reference.scope? model).toList
      | atom => (atom.fieldOriginsWith (fun _ => [])).filterMap fun (_, field) =>
          (model.lookupUniqueId field).toOption.map (·.repeatableScope)) expression

def boundFieldIds (expression : ScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies false (fun field => [field]) (·.boundFieldIds)
    (fun source => match source.key with | .field key => [key.id] | .literal .. => [])
    (fun atom => atom.fieldOriginsWith (fun _ => []) |>.map Prod.snd) expression

/-- Index and expanded operands require the addressed carrier to supply topology and selected reads. -/
def requiresAddressed (expression : ScalarTemporalExpression model) : Bool :=
  (scalarTemporalDependencies false (fun _ => []) (fun source =>
    [source.shape.operands.any fun | .field .. => false | _ => true]) (fun _ => [true]) (fun _ => []) expression).any id

def referencesWith (expression : ScalarTemporalExpression model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  (expression.dependenciesWith (fun source => [source == field])
    (fun source => [source.referencesWith field filterReads])
    (fun source => [source.referencesField field])).any id

def referencesField (expression : ScalarTemporalExpression model) (field : FieldId) : Bool :=
  expression.referencesWith field (·.referencesField field)

end ScalarTemporalExpression

namespace ScalarTemporalNumericAtom

/-- Reuse the complete recursive dependency traversal with consumer-owned projections of each retained source shape. -/
def dependenciesWith (expression : ScalarTemporalNumericAtom model)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (indexed : CheckedSemanticIndexSource model → List α)
    (numeric : HavingNumericAtomOf (ScalarTemporalExpression model) → List α :=
      fun atom => (atom.fieldOriginsWith (fun _ => [])).flatMap (field ∘ Prod.snd)) : List α :=
  scalarTemporalNumericDependencies false field entity indexed numeric expression

def hasHaving (expression : ScalarTemporalNumericAtom model) : Bool :=
  !(scalarTemporalNumericDependencies false (fun _ => ([] : List Unit))
    (fun source => if source.filters.any Option.isSome then [()] else []) (fun _ => []) (fun _ => []) expression).isEmpty

/-- Stored-text requirements include recursively nested temporal operands. -/
def storedTextFields (expression : ScalarTemporalNumericAtom model) : List FieldId :=
  scalarTemporalNumericDependencies true (fun field => [field]) (·.fieldIds)
    (fun source => match source.key with | .field key => [key.id] | .literal .. => []) (fun _ => []) expression

def fieldIds (expression : ScalarTemporalNumericAtom model) : List FieldId :=
  scalarTemporalNumericDependencies false (fun field => [field]) (·.fieldIds)
    (fun source => (model.fields.filter fun field => source.referencesField field.id).map (·.id))
    (fun atom => atom.fieldOriginsWith (fun _ => []) |>.map Prod.snd) expression

/-- Selected targets remain scheduler inputs while index and star selection bind their own rows (spec/08 §4). -/
def bindingScopes (expression : ScalarTemporalNumericAtom model) : List (List RepeatableLevel) :=
  scalarTemporalNumericDependencies false
    (fun field => ((model.lookupUniqueId field).toOption.map (·.repeatableScope)).toList)
    (·.bindingScopes)
    (·.bindingScopes)
    (fun atom => match atom with
      | .repetition reference => (reference.scope? model).toList
      | atom => (atom.fieldOriginsWith (fun _ => [])).filterMap fun (_, field) =>
          (model.lookupUniqueId field).toOption.map (·.repeatableScope)) expression

def boundFieldIds (expression : ScalarTemporalNumericAtom model) : List FieldId :=
  scalarTemporalNumericDependencies false (fun field => [field]) (·.boundFieldIds)
    (fun source => match source.key with | .field key => [key.id] | .literal .. => [])
    (fun atom => atom.fieldOriginsWith (fun _ => []) |>.map Prod.snd) expression

/-- Index and expanded operands require the addressed carrier to supply topology and selected reads. -/
def requiresAddressed (expression : ScalarTemporalNumericAtom model) : Bool :=
  (scalarTemporalNumericDependencies false (fun _ => []) (fun source =>
    [source.shape.operands.any fun | .field .. => false | _ => true]) (fun _ => [true]) (fun _ => []) expression).any id

def referencesWith (expression : ScalarTemporalNumericAtom model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  (expression.dependenciesWith (fun source => [source == field])
    (fun source => [source.referencesWith field filterReads])
    (fun source => [source.referencesField field])).any id

def referencesField (expression : ScalarTemporalNumericAtom model) (field : FieldId) : Bool :=
  expression.referencesWith field (·.referencesField field)

end ScalarTemporalNumericAtom

namespace CheckedConstructedDateComponents

def scalarCore (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) : ScalarTemporalExpression model :=
  .atom (.dateConstruction components)

def scalarFieldIds (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) : List FieldId :=
  components.scalarCore.fieldIds

def scalarBindingScopes (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) : List (List RepeatableLevel) :=
  components.scalarCore.bindingScopes

def scalarBoundFieldIds (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) : List FieldId :=
  components.scalarCore.boundFieldIds

end CheckedConstructedDateComponents

end A12Kernel
