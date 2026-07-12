import A12Kernel.Core

/-! # A12Kernel.Proofs.Verdict — laws of the truth and verdict algebras

These laws characterize the two finite algebras used by condition evaluation. The
counterexamples at the end keep tempting but invalid treatments of `unknown` and
polarity precedence visible beside the valid laws.
-/

namespace A12Kernel

namespace K

theorem and_commutative (a b : K) : and a b = and b a := by
  cases a <;> cases b <;> rfl

theorem and_associative (a b c : K) : and (and a b) c = and a (and b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem and_idempotent (a : K) : and a a = a := by
  cases a <;> rfl

theorem or_commutative (a b : K) : or a b = or b a := by
  cases a <;> cases b <;> rfl

theorem or_associative (a b c : K) : or (or a b) c = or a (or b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem or_idempotent (a : K) : or a a = a := by
  cases a <;> rfl

theorem and_tru_left (a : K) : and .tru a = a := by
  cases a <;> rfl

theorem and_tru_right (a : K) : and a .tru = a := by
  cases a <;> rfl

theorem and_fls_left (a : K) : and .fls a = .fls := by
  cases a <;> rfl

theorem and_fls_right (a : K) : and a .fls = .fls := by
  cases a <;> rfl

theorem or_fls_left (a : K) : or .fls a = a := by
  cases a <;> rfl

theorem or_fls_right (a : K) : or a .fls = a := by
  cases a <;> rfl

theorem or_tru_left (a : K) : or .tru a = .tru := by
  cases a <;> rfl

theorem or_tru_right (a : K) : or a .tru = .tru := by
  cases a <;> rfl

theorem and_absorbs_or (a b : K) : and a (or a b) = a := by
  cases a <;> cases b <;> rfl

theorem or_absorbs_and (a b : K) : or a (and a b) = a := by
  cases a <;> cases b <;> rfl

theorem and_distributes_over_or (a b c : K) :
    and a (or b c) = or (and a b) (and a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem or_distributes_over_and (a b c : K) :
    or a (and b c) = and (or a b) (or a c) := by
  cases a <;> cases b <;> cases c <;> rfl

end K

namespace Verdict

theorem conj_commutative (a b : Verdict) : conj a b = conj b a := by
  cases a <;> cases b <;> try rfl
  next p q => cases p <;> cases q <;> rfl

theorem conj_associative (a b c : Verdict) : conj (conj a b) c = conj a (conj b c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl
    | next p q r => cases p <;> cases q <;> cases r <;> rfl

theorem conj_idempotent (a : Verdict) : conj a a = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem disj_commutative (a b : Verdict) : disj a b = disj b a := by
  cases a <;> cases b <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl

theorem disj_associative (a b c : Verdict) : disj (disj a b) c = disj a (disj b c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl
    | next p q r => cases p <;> cases q <;> cases r <;> rfl

theorem disj_idempotent (a : Verdict) : disj a a = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem conj_fired_value_left (a : Verdict) : conj (.fired .value) a = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem conj_fired_value_right (a : Verdict) : conj a (.fired .value) = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem conj_notFired_left (a : Verdict) : conj .notFired a = .notFired := by
  cases a <;> rfl

theorem conj_notFired_right (a : Verdict) : conj a .notFired = .notFired := by
  cases a <;> rfl

theorem disj_notFired_left (a : Verdict) : disj .notFired a = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem disj_notFired_right (a : Verdict) : disj a .notFired = a := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem disj_fired_value_left (a : Verdict) : disj (.fired .value) a = .fired .value := by
  cases a <;> rfl

theorem disj_fired_value_right (a : Verdict) : disj a (.fired .value) = .fired .value := by
  cases a <;> try rfl
  next p => cases p <;> rfl

theorem conj_absorbs_disj (a b : Verdict) : conj a (disj a b) = a := by
  cases a <;> cases b <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl

theorem disj_absorbs_conj (a b : Verdict) : disj a (conj a b) = a := by
  cases a <;> cases b <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl

theorem conj_distributes_over_disj (a b c : Verdict) :
    conj a (disj b c) = disj (conj a b) (conj a c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl
    | next p q r => cases p <;> cases q <;> cases r <;> rfl

theorem disj_distributes_over_conj (a b c : Verdict) :
    disj a (conj b c) = conj (disj a b) (disj a c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  all_goals
    first
    | next p => cases p <;> rfl
    | next p q => cases p <;> cases q <;> rfl
    | next p q r => cases p <;> cases q <;> cases r <;> rfl

end Verdict

/-! ## Checked non-laws

`unknown` is not an absorber: decisive operands suppress it. Polarity precedence is
also connective-specific rather than a single global winner.
-/

example : K.and .unknown .fls ≠ .unknown := by decide
example : K.or .unknown .tru ≠ .unknown := by decide

example : Verdict.conj .unknown .notFired ≠ .unknown := by decide
example : Verdict.disj .unknown (.fired .omission) ≠ .unknown := by decide

example : Verdict.conj (.fired .value) (.fired .omission) ≠ .fired .value := by decide
example : Verdict.disj (.fired .value) (.fired .omission) ≠ .fired .omission := by decide

end A12Kernel
