import A12Kernel.Elaboration.ValidationRule.AssemblyError
import A12Kernel.Semantics.ValidationRule

/-! # The placement of a rule's error entity

A rule reports on a field or on a group. This module resolves that entity against the model
into the scope its pointer carries and the levels it pins without iterating.
-/

namespace A12Kernel

/-- Where a rule's error entity sits. A field keeps its declaration. A group sits at its own path with
every repeatable level of that path; when the group itself repeats, its own level is not iterated: the
pointer names its first row, a field read at that level reads that row, and the group's own presence
reads every row ([checkpoint](../../../docs/sources/key-join-and-parallel-probes.md#src-group-target-nested-join),
`group-target` and `group-level`). -/
inductive RuleErrorPlacement where
  | field (declaration : FlatFieldDecl)
  | group (path : GroupPath) (repeatableScope : List RepeatableLevel)
      (ownLevel : Option RepeatableLevel)
  deriving Repr, DecidableEq

namespace RuleErrorPlacement

def entity : RuleErrorPlacement → RuleErrorEntity
  | .field declaration => .field declaration.id
  | .group path _ _ => .group path

/-- The group the entity's static reads and its root gate are judged from. -/
def groupPath : RuleErrorPlacement → GroupPath
  | .field declaration => declaration.groupPath
  | .group path _ _ => path

/-- Every repeatable level the entity's pointer carries. -/
def repeatableScope : RuleErrorPlacement → List RepeatableLevel
  | .field declaration => declaration.repeatableScope
  | .group _ scope _ => scope

/-- The levels pinned to the first row without iteration. -/
def unindexed : RuleErrorPlacement → List RepeatableLevel
  | .field _ => []
  | .group _ _ ownLevel => ownLevel.toList

def fieldDeclaration? : RuleErrorPlacement → Option FlatFieldDecl
  | .field declaration => some declaration
  | .group _ _ _ => none

end RuleErrorPlacement

/-- Resolve a rule's error entity against the model. The root is placed like any other group: below
the root the Kernel judges a rule reporting on it as an ordinary group
([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths)). -/
def FlatModel.ruleErrorPlacement (model : FlatModel) :
    RuleErrorEntity → Except FlatRuleAssemblyError RuleErrorPlacement
  | .field field =>
      match model.lookupUniqueId field with
      | .ok declaration => .ok (.field declaration)
      | .error error => .error (.errorField error)
  | .group path =>
      if !model.hasGroupPath path then .error (.groupErrorTarget path .unknown)
      else .ok (.group path (model.repeatableScopeForGroupPath path)
        ((model.repeatableGroups.find? (·.path == path)).map (·.level)))

end A12Kernel
