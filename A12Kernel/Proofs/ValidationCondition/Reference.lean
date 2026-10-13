import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Proofs.MessagePointer

/-! # A12Kernel.Proofs.ValidationCondition.Reference — structural reference laws

The ordinary and reopened pointer constructors have exactness and arity laws. Selected references additionally use the cache laws in `Proofs.MessageIndex`. The connective law states the projection's defining property: a reference exists by being authored, never by being decisive.
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

/-- A successful token-star projection always retains the selected field pointer. Explain consumers may therefore inspect additional `Having` dependencies without losing the value source that the filter selected. -/
theorem checkedTokenEntityOperand_star_sourcePointer
    (source : CheckedTokenStarSource model) (environment : Env)
    (pointers : List MessagePointer)
    (projected :
      CheckedTokenEntityOperand.referencePointers environment (.star source) =
        .ok pointers) :
    ∃ pointer,
      starFieldPointer source.source environment = .ok pointer ∧
        pointer ∈ pointers := by
  change source.referencePointers environment = .ok pointers at projected
  unfold CheckedTokenStarSource.referencePointers at projected
  cases selectedProjection : starFieldPointer source.source environment with
  | error error =>
      rw [selectedProjection] at projected
      simp only [Bind.bind, Except.bind] at projected
      cases projected
  | ok selected =>
      rw [selectedProjection] at projected
      refine ⟨selected, rfl, ?_⟩
      simp only [Bind.bind, Except.bind, pure, Except.pure] at projected
      split at projected
      · cases projected
      · simp only [Except.ok.injEq] at projected
        rw [← projected]
        simp

private theorem mapM_pointers_exact
    (project : FlatFieldDecl → Except ReferenceProjectionError MessagePointer) :
    ∀ (declarations : List FlatFieldDecl),
      (∀ declaration ∈ declarations, ∀ pointer, project declaration = .ok pointer →
        pointer.toCellAddr?.isSome = true) →
      ∀ (pointers : List MessagePointer), declarations.mapM project = .ok pointers →
        ∀ pointer ∈ pointers, pointer.toCellAddr?.isSome = true := by
  intro declarations
  induction declarations with
  | nil =>
      intro _ pointers projected
      change Except.ok [] = Except.ok pointers at projected
      cases projected
      simp
  | cons declaration remaining inductionHypothesis =>
      intro exact pointers projected
      simp only [List.mapM_cons] at projected
      cases head : project declaration with
      | error _ => simp [head, Bind.bind, Except.bind] at projected
      | ok pointer =>
          cases tail : remaining.mapM project with
          | error _ => simp [head, tail, Bind.bind, Except.bind] at projected
          | ok rest =>
              simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure,
                Except.ok.injEq] at projected
              subst projected
              intro candidate member
              rcases List.mem_cons.mp member with equal | member
              · rw [equal]
                exact exact declaration List.mem_cons_self pointer head
              · exact inductionHypothesis
                  (fun other inRemaining => exact other (List.mem_cons_of_mem _ inRemaining))
                  rest tail candidate member

/-- A sieved family emits only exact document addresses wherever the firing environment binds every
repeatable level of each referenced declaration, the counterpart of
[`reopenedFieldPointer_notExact`](A12Kernel.reopenedFieldPointer_notExact). Only a subtree field below a
level the rule does not bind is wildcarded. -/
theorem sievedFieldPointers_exact_of_bound (model : FlatModel)
    (references : FlatFieldDecl → Bool) (environment : Env)
    (bound : ∀ declaration ∈ model.fields, references declaration = true →
      environment.bindsScope declaration = true)
    (pointers : List MessagePointer)
    (projected : sievedFieldPointers model references environment = .ok pointers) :
    ∀ pointer ∈ pointers, pointer.toCellAddr?.isSome = true := by
  refine mapM_pointers_exact (sievedFieldPointer · environment) _ ?_ pointers projected
  intro declaration member pointer head
  obtain ⟨declared, referenced⟩ := List.mem_filter.mp member
  unfold sievedFieldPointer at head
  rw [if_pos (bound declaration declared referenced)] at head
  exact (concreteFieldPointer_exact declaration environment pointer head).2

/-- The projection is blind to the connective, which is the precise sense in which it is structural: a reference is authored, not decisive, so an `Or` branch that never decided still contributes. -/
theorem referencePointers_connective_blind (left right : ValidationCondition model)
    (environment : Env) (inputs : Option MessageReferenceInputs := none) :
    ValidationCondition.referencePointers (.and left right) environment inputs =
      ValidationCondition.referencePointers (.or left right) environment inputs :=
  rfl

end A12Kernel
