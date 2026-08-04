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

/-- A starred reference never collapses to an exact address, because the certificate's own `firstStarWithin` obligation guarantees at least one reopened axis. A consumer that treats a reference as a cell address is therefore wrong on exactly the starred case. -/
theorem starFieldPointer_notExact (checked : CheckedStarFieldPath model)
    (environment : Env) (pointer : MessagePointer)
    (projected : starFieldPointer checked environment = .ok pointer) :
    pointer.toCellAddr? = none := by
  unfold starFieldPointer at projected
  cases resolved : environment.pathForScope checked.bindingScope with
  | error _ => simp [resolved] at projected
  | ok bound =>
      simp only [resolved, Except.ok.injEq] at projected
      subst projected
      obtain ⟨reopened, hReopened⟩ :
          ∃ reopened,
            checked.path.axes.length - checked.path.firstStar = reopened + 1 :=
        ⟨checked.path.axes.length - checked.path.firstStar - 1, by
          have := checked.firstStarWithin; omega⟩
      simp [MessagePointer.toCellAddr?, hReopened, List.replicate_succ,
        toConcretePath_concrete_append_wildcard]

/-- A starred pointer carries exactly one coordinate per repeatable level of its declaration: the bound prefix plus every reopened axis. This is the arity `MessagePointer` promises, derived from the checked path rather than assumed. -/
theorem starFieldPointer_arity (checked : CheckedStarFieldPath model)
    (environment : Env) (pointer : MessagePointer)
    (projected : starFieldPointer checked environment = .ok pointer) :
    pointer.coordinates.length =
      checked.declaration.repeatableScope.length := by
  unfold starFieldPointer at projected
  cases resolved : environment.pathForScope checked.bindingScope with
  | error _ => simp [resolved] at projected
  | ok bound =>
      simp only [resolved, Except.ok.injEq] at projected
      subst projected
      have boundLength :=
        env_pathForScope_length environment checked.bindingScope bound resolved
      have ancestry := checked.ancestryOwned
      have axesLength : checked.declaration.repeatableScope.length =
          checked.path.axes.length := by
        rw [← ancestry, List.length_map]
      have := checked.firstStarWithin
      simp [CheckedStarFieldPath.bindingScope] at boundLength
      simp [boundLength, axesLength]
      omega

/-- The projection is blind to the connective, which is the precise sense in which it is structural: a reference is authored, not decisive, so an `Or` branch that never decided still contributes. -/
theorem referencePointers_connective_blind (left right : ValidationCondition model)
    (environment : Env) :
    ValidationCondition.referencePointers (.and left right) environment =
      ValidationCondition.referencePointers (.or left right) environment :=
  rfl

end A12Kernel
