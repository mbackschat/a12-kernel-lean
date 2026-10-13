import A12Kernel.Elaboration.MessageAuthoringContext
import A12Kernel.Elaboration.MessageParameterSyntax
import A12Kernel.Elaboration.IndexParameterResolution
import A12Kernel.Elaboration.IndexParameterSuffix

namespace A12Kernel

structure MessageIndexBinding where
  groupPath : GroupPath
  /-- The indexed group's repeatable declaration; `none` for a non-repeatable indexed group, whose
  parameter meets the declaration-shape gate instead of the iteration one. -/
  repeatable : Option RepeatableGroupDecl
  declaration : FlatFieldDecl
  deriving Repr, DecidableEq

/-- Index parameters resolve short names only on the error path
(FullChecks_ErrorTextParameterParser.checkIndexFieldRef), whether or not the indexed group repeats. -/
def messageIndexBindings (model : FlatModel) (name : String) : List MessageIndexBinding :=
  let named (field : FieldId) := (model.fields.find? (·.id == field)).filter (·.name == name)
  (model.repeatableGroups.filterMap fun group => do
    let declaration ← named (← group.indexField)
    some { groupPath := group.path, repeatable := some group, declaration }) ++
  model.nonrepeatableIndexFields.filterMap fun (groupPath, field) => do
    let declaration ← named field
    some { groupPath, repeatable := none, declaration }

def messageErrorPathIndices (condition : ValidationMessageCondition model)
    (name : String) : List MessageIndexBinding :=
  (messageIndexBindings model name).filter fun binding =>
    condition.errorDeclaration?.any (binding.groupPath.isPrefixOf ·.groupPath)

inductive IndexMessageAuthoringError where
  | contextRequired
  | unsupportedReferenceMetadata
  | unsupportedIndexType
  | missingCategoryName
  | diagnostic (diagnostic : KernelStaticDiagnostic)
  deriving Repr, DecidableEq

private def MessageIndexBinding.repeats (binding : MessageIndexBinding) : Bool :=
  binding.repeatable.any (·.repeatability.any (· > 1))

private def MessageIndexBinding.fieldType (binding : MessageIndexBinding) : IndexFieldType :=
  match binding.declaration.enumeration with
  | none => .other
  | some enumeration => .enumeration enumeration.storedTokens.length enumeration.defaultStoredToken.isSome

private def MessageIndexBinding.suffixDeclaration (binding : MessageIndexBinding)
    (suffix : MessageFieldSuffix) : ReferencedDeclaration :=
  match binding.declaration.enumeration with
  | none => { isEnumeration := false, declaresCategory := false }
  | some enumeration =>
      let category : Option EnumerationCategoryDeclaration := match suffix with
        | .category name => enumeration.categories.find? (fun entry => entry.name == name)
        | _ => none
      { isEnumeration := true
        declaresCategory := category.isSome
        values := enumeration.storedTokens
        categoryValues := category.map (·.tokens) |>.getD []
        displayMapping := enumeration.displayFacts.flatMap fun fact =>
          [fact.locale, fact.stored, fact.display] }

/-- Ancestor index references retain every authored mode. In particular, a plain read cannot hide a
second starred or keyed read of the same index (ReferencedIdsUtil.createAllIndexFieldEntityIds).

The candidates are visited in full-name order, not declaration order (row `o01` in the
[checkpoint](../../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15)).
`String` order here compares code points where the Kernel's Java strings compare UTF-16 units; the
two can differ only on a name holding a character beyond the Basic Multilingual Plane, where this
order is unmeasured. -/
def messageReferencedIndices (condition : ValidationMessageCondition model) (name : String) :
    Except IndexMessageAuthoringError (List (MessageIndexBinding × ReferencedIndexField)) := do
  let candidates := (messageIndexBindings model name).mergeSort fun left right =>
    String.intercalate "/" left.declaration.path ≤ String.intercalate "/" right.declaration.path
  let entries ← candidates.mapM fun binding => do
    let some referenced := condition.indexReferenced? binding.groupPath
      | throw .unsupportedReferenceMetadata
    if !referenced then pure none else
      -- Only the repeatable branch reads iteration (`repeatabilityRefusal`).
      let some nonIterating := match binding.repeatable with
          | some group => condition.indexNonIterating? binding.groupPath group.level
          | none => some false
        | throw .unsupportedReferenceMetadata
      pure (some (binding, {
        repeatable := binding.repeats
        iterating := !nonIterating
        fieldType := binding.fieldType }))
  pure (entries.filterMap id)

private def parameterSuffix : MessageFieldSuffix → ParameterSuffix
  | .none => .absent
  | .value => .value
  | .category _ => .category

def messageIndexReferenceRefusal (condition : ValidationMessageCondition model)
    (binding : MessageIndexBinding) (name : String) (suffix : MessageFieldSuffix) :
    Except IndexMessageAuthoringError Unit := do
  let references ← messageReferencedIndices condition name
  if let some refusal := repeatabilityScan binding.repeats (references.map (·.2)) then
    throw (.diagnostic refusal)
  if suffix == .category "" then throw .missingCategoryName
  if let some refusal := suffixRefusal (parameterSuffix suffix)
      (references.map (fun entry => entry.1.suffixDeclaration suffix)) then
    throw (.diagnostic refusal)

structure CheckedMessageIndex (model : FlatModel) (condition : ValidationMessageCondition model) where
  name : String
  binding : MessageIndexBinding
  suffix : MessageFieldSuffix
  resolved : messageErrorPathIndices condition name = [binding]
  checked : messageIndexReferenceRefusal condition binding name suffix = .ok ()

def checkMessageIndex (condition : ValidationMessageCondition model)
    (name : String) (suffix : MessageFieldSuffix) :
    Except IndexMessageAuthoringError (CheckedMessageIndex model condition) := do
  if condition.errorDeclaration?.isNone then throw .contextRequired
  if let some refusal := resolutionRefusal {
      matching := (messageErrorPathIndices condition name).length } then
    throw (.diagnostic refusal)
  match hResolved : messageErrorPathIndices condition name with
  | [] => throw (.diagnostic .indexFieldUnresolved)
  | _ :: _ :: _ => throw (.diagnostic .indexFieldAmbiguous)
  | [binding] =>
      match hChecked : messageIndexReferenceRefusal condition binding name suffix with
      | .error error => throw error
      | .ok () =>
          match binding.declaration.policy.kind with
          | .string | .enumeration =>
              pure { name, binding, suffix, resolved := hResolved, checked := hChecked }
          | _ => throw .unsupportedIndexType

end A12Kernel
