import A12Kernel.Elaboration.PartialSemanticIndex
import A12Kernel.Elaboration.CheckedGroupPresence

namespace A12Kernel
namespace CheckedKeyedEntityExtent

def isGroup (source : CheckedKeyedEntityExtent model) : Bool :=
  match source.target with | .group _ | .starredGroup _ => true | .star _ => false

def isStarredGroup (source : CheckedKeyedEntityExtent model) : Bool :=
  match source.target with | .starredGroup _ => true | .group _ | .star _ => false

/-- Group guards count instantiated group instances, not the missing declared field slots used by
field-fill quantifiers (spec/03 group lists; spec/08 keyed-parent stars). -/
def groupEnvironments (source : CheckedKeyedEntityExtent model) (document : Document) (selected : Env) :
    Except CheckedAddressingError (List Env) := do
  match source.target with
  | .group _ => pure [selected]
  | .star _ => throw (.addressing (.unsupportedGroupOperand source.groupPath))
  | .starredGroup path =>
      let some axes := model.repeatableAxesForScope? (model.repeatableScopeForGroupPath path)
        | throw (.addressing (.unsupportedGroupOperand path))
      let (rows, _) ← StarAxes.resolveOperandExtent axes document selected source.boundLevelCount
        |>.mapError .addressing
      pure rows

/-- Selection failure is unavailable before group content is classified. A missing scalar group
is cleanly empty, while a missing starred selection contributes no group instances. -/
def validationGroupStates (source : CheckedKeyedEntityExtent model) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError (Option (List GroupPresenceState)) := do
  let selected ← source.selectWith document.source.toDocument .validation (document.resolveSemanticIndexColumnWith document.read)
    outer (document.computationContextAt outer).read (document.computationContextAt outer).storedText
  match selected with
  | .unknown _ | .poison _ => pure none
  | .empty => pure (some (if source.isStarredGroup then [] else
      [{ content := false, erroneous := false, relevance := .fullyRelevant }]))
  | .value environment =>
      let rows ← source.groupEnvironments document.source.toDocument environment
      some <$> rows.mapM fun row => do
        let input ← document.groupPresenceInput source.groupPath row .fullyRelevant false |>.mapError .group
        pure input.derive

def validationGroupPresence (source : CheckedKeyedEntityExtent model) (operator : GroupPresenceOperator)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict := do
  match ← source.validationGroupStates document outer with
  | none => pure .unknown
  | some [state] => pure (operator.eval state)
  | _ => throw (.addressing (.unsupportedGroupOperand source.groupPath))

/-- Partial selected-group state preserves unavailable selection and incomplete missing-key
coverage before a consuming predicate chooses filledness or emptiness (spec/10 §5). -/
def partialGroupState (source : CheckedKeyedEntityExtent model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option GroupPresenceState) := do
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  match ← source.selectPartial view outer read with
  | none | some (.unknown _) | some (.poison _) => pure none
  | some .empty =>
      let bound := source.selection.indexDeclaration.repeatableScope.dropLast
      let complete := source.declarations.all fun declaration =>
        view.relevance.coversValueListExtent model declaration.path bound
          (declaration.repeatableScope.drop bound.length) outer
      pure (some {
        content := false, erroneous := false
        relevance := if complete then .fullyRelevant else .partlyRelevant })
  | some (.value environment) =>
      let input ← view.groupPresenceInput source.groupPath environment false |>.mapError .group
      pure (some input.derive)

/-- Key-only coverage can establish filledness but cannot establish empty descendants. -/
def partialGroupPresence (source : CheckedKeyedEntityExtent model) (operator : GroupPresenceOperator)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError Verdict := do
  pure ((← source.partialGroupState document scope outer read).map operator.eval |>.getD .unknown)

/-- Index poison precedes the ordinary group-content policy. That policy treats malformed input
and failed computed cells differently, rather than propagating every descendant as field poison. -/
def computationGroupPresence (source : CheckedKeyedEntityExtent model) (operator : GroupPresenceOperator)
    (context : ScalarComputationContext) (column : SemanticIndexColumnReader) :
    Except CheckedAddressingError ComputationConditionResult := do
  let some addressed := context.addressed | throw (.checkedDocumentRequired source.groupPath)
  let selected ← source.selectWith addressed.document .computation column context.row context.read context.storedText
  match selected with
  | .unknown cause | .poison cause => pure (.poison cause)
  | .empty => pure (operator.evalComputation [] false)
  | .value environment =>
      let rows ← source.groupEnvironments addressed.document environment
      for row in rows do
        let result ← (model.computationGroupSource source.groupPath).eval .filled
          addressed.document addressed.read row |>.mapError .environment
        if result == .holds then
          return if operator == .filled then .holds else .notTrue
      pure (if operator == .filled then .notTrue else .holds)

end CheckedKeyedEntityExtent
end A12Kernel
