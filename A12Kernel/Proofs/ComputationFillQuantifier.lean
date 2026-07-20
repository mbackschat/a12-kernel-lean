import A12Kernel.Semantics.ComputationFillQuantifier

/-! # Resolved computation field-fill quantifier laws

These laws characterize ordered computation-side scans after expansion. They prove universal poison-head preservation, representative deciding-prefix suffix equations, and the declared-versus-instantiated range split. They do not prove arbitrary-prefix transformations, group/path expansion, filtering, formal checking, validation truth or polarity, authored legality, or correspondence to the external kernel.
-/

namespace A12Kernel

/-- Every field-fill operator preserves the exact cause of a poison reached at the head. -/
theorem computationFillQuantifier_poisonHead_preserves
    (operator : ComputationFieldFillQuantifier)
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    operator.eval (.poison cause :: suffix) = .poison cause := by
  cases operator <;> rfl

/-- An instantiated empty head decides `AllFieldsFilled`; the suffix is unread. -/
theorem allFieldsFilled_emptyHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.allFieldsFilled.eval
      (.empty :: suffix) = .notTrue := by
  rfl

/-- An instantiated empty head decides `NotAllFieldsFilled`; the suffix is unread. -/
theorem notAllFieldsFilled_emptyHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.notAllFieldsFilled.eval
      (.empty :: suffix) = .holds := by
  rfl

/-- A filled head decides `NoFieldFilled`; the suffix is unread. -/
theorem noFieldFilled_filledHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.noFieldFilled.eval
      (.filled :: suffix) = .notTrue := by
  rfl

/-- A filled head decides `AtLeastOneFieldFilled`; the suffix is unread. -/
theorem atLeastOneFieldFilled_filledHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.atLeastOneFieldFilled.eval
      (.filled :: suffix) = .holds := by
  rfl

/-- Two leading filled slots decide `MoreThanOneFieldFilled`; the suffix is unread. -/
theorem moreThanOneFieldFilled_twoFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.moreThanOneFieldFilled.eval
      (.filled :: .filled :: suffix) = .holds := by
  rfl

/-- Two leading filled slots decide `NotExactlyOneFieldFilled`; the suffix is unread. -/
theorem notExactlyOneFieldFilled_twoFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval
      (.filled :: .filled :: suffix) = .holds := by
  rfl

/-- Reaching an empty and then a filled slot decides `FieldsNotCollectivelyFilled`; the suffix is unread. -/
theorem fieldsNotCollectivelyFilled_emptyFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.fieldsNotCollectivelyFilled.eval
      (.empty :: .filled :: suffix) = .holds := by
  rfl

/-- Reaching a filled and then an empty slot also decides `FieldsNotCollectivelyFilled`; the suffix is unread. -/
theorem fieldsNotCollectivelyFilled_filledEmptyPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.fieldsNotCollectivelyFilled.eval
      (.filled :: .empty :: suffix) = .holds := by
  rfl

/-- Declared-range predicates observe an uninstantiated head as a deciding empty slot. -/
theorem computationFillQuantifier_declaredRange_observesUninstantiated
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.allFieldsFilled.eval
        (.uninstantiated :: suffix) = .notTrue ∧
      ComputationFieldFillQuantifier.notAllFieldsFilled.eval
        (.uninstantiated :: suffix) = .holds := by
  constructor <;> rfl

/-- Every instantiated-range predicate skips an uninstantiated head without reading a cell. -/
theorem computationFillQuantifier_instantiatedRange_skipsUninstantiated
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.noFieldFilled.eval
        (.uninstantiated :: suffix) =
          ComputationFieldFillQuantifier.noFieldFilled.eval suffix ∧
      ComputationFieldFillQuantifier.atLeastOneFieldFilled.eval
        (.uninstantiated :: suffix) =
          ComputationFieldFillQuantifier.atLeastOneFieldFilled.eval suffix ∧
      ComputationFieldFillQuantifier.moreThanOneFieldFilled.eval
        (.uninstantiated :: suffix) =
          ComputationFieldFillQuantifier.moreThanOneFieldFilled.eval suffix ∧
      ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval
        (.uninstantiated :: suffix) =
          ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval suffix := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-- The mixed operator can combine an uninstantiated declared empty with a later instantiated filled slot, then ignore the suffix. -/
theorem fieldsNotCollectivelyFilled_uninstantiatedFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.fieldsNotCollectivelyFilled.eval
      (.uninstantiated :: .filled :: suffix) = .holds := by
  rfl

/-- `NotExactlyOneFieldFilled` distinguishes zero, exactly one, and at least two filled slots. -/
theorem notExactlyOneFieldFilled_zeroOneTwo
    (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval [] = .holds ∧
      ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval
        [.filled] = .notTrue ∧
      ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval
        (.filled :: .filled :: suffix) = .holds := by
  constructor
  · rfl
  constructor <;> rfl

/-- A poison reached after only one filled slot prevents both two-filled predicates from deciding. -/
theorem secondFilledPredicates_oneFilledThenPoison_preserve
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.moreThanOneFieldFilled.eval
        [.filled, .poison cause] = .poison cause ∧
      ComputationFieldFillQuantifier.notExactlyOneFieldFilled.eval
        (.filled :: .poison cause :: suffix) = .poison cause := by
  constructor <;> rfl

/-- A filled witness alone does not let the mixed predicate skip a poison before any declared empty witness. -/
theorem fieldsNotCollectivelyFilled_filledThenPoison_preserves
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    ComputationFieldFillQuantifier.fieldsNotCollectivelyFilled.eval
      (.filled :: .poison cause :: suffix) = .poison cause := by
  rfl

/-- Read order is observable: a filled decision before poison differs from the same two slots reversed. -/
theorem computationFillQuantifier_readOrderObservable
    (cause : FormalCause) :
    ComputationFieldFillQuantifier.atLeastOneFieldFilled.eval
        [.filled, .poison cause] ≠
      ComputationFieldFillQuantifier.atLeastOneFieldFilled.eval
        [.poison cause, .filled] := by
  intro impossible
  cases impossible

end A12Kernel
