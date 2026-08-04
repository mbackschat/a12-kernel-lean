import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Proofs.MessagePointer

/-! # A12Kernel.Proofs.ValidationCondition.Reference — structural reference laws

The two pointer constructors are the whole projection's only producers, so their exactness and arity laws hold for every reference the tree can emit. The connective law states the projection's defining property: a reference exists by being authored, never by being decisive.
-/

namespace A12Kernel

/-- Projecting a scope preserves its length, which is what makes one coordinate per repeatable level a derivable arity rather than a convention. -/
private theorem env_pathForScope_length (environment : Env) :
    ∀ (levels : List RepeatableLevel) (path : List Nat),
      environment.pathForScope levels = .ok path → path.length = levels.length := by
  intro levels
  induction levels with
  | nil =>
      intro path resolved
      simp only [Env.pathForScope, pure, Except.pure, Except.ok.injEq] at resolved
      subst resolved
      rfl
  | cons level remaining inductionHypothesis =>
      intro path resolved
      simp only [Env.pathForScope, bind, Except.bind, pure, Except.pure] at resolved
      cases binding : environment.bindingAt level with
      | error _ => simp [binding] at resolved
      | ok coordinate =>
          cases tail : environment.pathForScope remaining with
          | error _ => simp [binding, tail] at resolved
          | ok tailPath =>
              simp only [binding, tail, Except.ok.injEq] at resolved
              subst resolved
              simp [inductionHypothesis tailPath tail]

/-- Once a wildcard appears, no exact address can be recovered from the remaining coordinates. -/
private theorem toConcretePath_concrete_append_wildcard (concretePrefix : List Nat)
    (rest : List MessageRepetitionCoordinate) :
    MessagePointer.toConcretePath?
        (concretePrefix.map .concrete ++ .wildcard :: rest) = none := by
  induction concretePrefix with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [MessagePointer.toConcretePath?, inductionHypothesis]

/-- An unstarred reference names one exact instance: its pointer keeps the declaration's identity and recovers a document address. -/
theorem concreteFieldPointer_exact (declaration : FlatFieldDecl) (environment : Env)
    (pointer : MessagePointer)
    (projected : concreteFieldPointer declaration environment = .ok pointer) :
    pointer.field = declaration.id ∧ pointer.toCellAddr?.isSome = true := by
  unfold concreteFieldPointer at projected
  cases resolved : environment.pathForScope declaration.repeatableScope with
  | error _ => simp [resolved] at projected
  | ok path =>
      simp only [resolved, Except.ok.injEq] at projected
      subst projected
      exact ⟨rfl, by simp [messagePointer_toCellAddr_ofCellAddr]⟩

/-- A reopened reference never collapses to an exact address. The guarantee is the function's own admission guard rather than any caller's obligation: it only succeeds when the declaration's scope extends past the bound prefix, so at least one wildcard is always present. A consumer that treats a reference as a cell address is therefore wrong on exactly the reopened case. -/
theorem reopenedFieldPointer_notExact (declaration : FlatFieldDecl)
    (boundCount : Nat) (environment : Env) (pointer : MessagePointer)
    (projected : reopenedFieldPointer declaration boundCount environment = .ok pointer) :
    pointer.toCellAddr? = none := by
  unfold reopenedFieldPointer at projected
  split at projected
  case isTrue => simp at projected
  case isFalse reopened =>
      cases resolved :
          environment.pathForScope (declaration.repeatableScope.take boundCount) with
      | error _ => simp [resolved] at projected
      | ok bound =>
          simp only [resolved, Except.ok.injEq] at projected
          subst projected
          obtain ⟨remaining, hRemaining⟩ :
              ∃ remaining,
                declaration.repeatableScope.length - boundCount = remaining + 1 :=
            ⟨declaration.repeatableScope.length - boundCount - 1, by omega⟩
          simp [MessagePointer.toCellAddr?, hRemaining, List.replicate_succ,
            toConcretePath_concrete_append_wildcard]

/-- A reopened pointer carries exactly one coordinate per repeatable level of its declaration: the bound prefix plus every reopened level. This is the arity `MessagePointer` promises, derived rather than assumed, and it holds for a starred group's deeper descendant as much as for the starred field itself. -/
theorem reopenedFieldPointer_arity (declaration : FlatFieldDecl)
    (boundCount : Nat) (environment : Env) (pointer : MessagePointer)
    (projected : reopenedFieldPointer declaration boundCount environment = .ok pointer) :
    pointer.coordinates.length = declaration.repeatableScope.length := by
  unfold reopenedFieldPointer at projected
  split at projected
  case isTrue => simp at projected
  case isFalse reopened =>
      cases resolved :
          environment.pathForScope (declaration.repeatableScope.take boundCount) with
      | error _ => simp [resolved] at projected
      | ok bound =>
          simp only [resolved, Except.ok.injEq] at projected
          subst projected
          have boundLength := env_pathForScope_length environment
            (declaration.repeatableScope.take boundCount) bound resolved
          simp only [List.length_take] at boundLength
          simp only [List.length_append, List.length_map,
            List.length_replicate, boundLength]
          omega

/-- The starred-field law is a specialization: its certificate's `ancestryOwned` and `firstStarWithin` obligations are what make the shared admission guard succeed, so no separate proof is needed. -/
theorem starFieldPointer_notExact (checked : CheckedStarFieldPath model)
    (environment : Env) (pointer : MessagePointer)
    (projected : starFieldPointer checked environment = .ok pointer) :
    pointer.toCellAddr? = none :=
  reopenedFieldPointer_notExact _ _ _ _ projected

theorem starFieldPointer_arity (checked : CheckedStarFieldPath model)
    (environment : Env) (pointer : MessagePointer)
    (projected : starFieldPointer checked environment = .ok pointer) :
    pointer.coordinates.length =
      checked.declaration.repeatableScope.length :=
  reopenedFieldPointer_arity _ _ _ _ projected

/-- The projection is blind to the connective, which is the precise sense in which it is structural: a reference is authored, not decisive, so an `Or` branch that never decided still contributes. -/
theorem referencePointers_connective_blind (left right : ValidationCondition model)
    (environment : Env) :
    ValidationCondition.referencePointers (.and left right) environment =
      ValidationCondition.referencePointers (.or left right) environment :=
  rfl

end A12Kernel
