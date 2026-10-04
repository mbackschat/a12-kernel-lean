import A12Kernel.Semantics.ComputationFillQuantifier

/-! # Resolved computation field-fill quantifier laws

These laws characterize ordered computation-side scans after expansion. They prove universal poison-head preservation, representative deciding-prefix suffix equations, and the declared-versus-instantiated range split. They do not prove arbitrary-prefix transformations, group/path expansion, filtering, formal checking, validation truth or polarity, authored legality, or correspondence to the external kernel.
-/

namespace A12Kernel

/-- Every field-fill operator preserves the exact cause of a poison reached at the head. -/
theorem computationFillQuantifier_poisonHead_preserves
    (operator : FieldFillQuantifier)
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    operator.evalComputation (.poison cause :: suffix) = .poison cause := by
  cases operator <;> rfl

/-- An instantiated empty head decides `AllFieldsFilled`; the suffix is unread. -/
theorem allFieldsFilled_emptyHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.allFieldsFilled.evalComputation
      (.empty :: suffix) = .notTrue := by
  rfl

/-- An instantiated empty head decides `NotAllFieldsFilled`; the suffix is unread. -/
theorem notAllFieldsFilled_emptyHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.notAllFieldsFilled.evalComputation
      (.empty :: suffix) = .holds := by
  rfl

/-- A filled head decides `NoFieldFilled`; the suffix is unread. -/
theorem noFieldFilled_filledHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.noFieldFilled.evalComputation
      (.filled :: suffix) = .notTrue := by
  rfl

/-- A filled head decides `AtLeastOneFieldFilled`; the suffix is unread. -/
theorem atLeastOneFieldFilled_filledHead_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
      (.filled :: suffix) = .holds := by
  rfl

/-- Two leading filled slots decide `MoreThanOneFieldFilled`; the suffix is unread. -/
theorem moreThanOneFieldFilled_twoFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.moreThanOneFieldFilled.evalComputation
      (.filled :: .filled :: suffix) = .holds := by
  rfl

/-- Two leading filled slots decide `NotExactlyOneFieldFilled`; the suffix is unread. -/
theorem notExactlyOneFieldFilled_twoFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation
      (.filled :: .filled :: suffix) = .holds := by
  rfl

/-- Reaching an empty and then a filled slot decides `FieldsNotCollectivelyFilled`; the suffix is unread. -/
theorem fieldsNotCollectivelyFilled_emptyFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalComputation
      (.empty :: .filled :: suffix) = .holds := by
  rfl

/-- Reaching a filled and then an empty slot also decides `FieldsNotCollectivelyFilled`; the suffix is unread. -/
theorem fieldsNotCollectivelyFilled_filledEmptyPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalComputation
      (.filled :: .empty :: suffix) = .holds := by
  rfl

/-- Declared-range predicates observe an uninstantiated head as a deciding empty slot. -/
theorem computationFillQuantifier_declaredRange_observesUninstantiated
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.allFieldsFilled.evalComputation
        (.uninstantiated :: suffix) = .notTrue ∧
      FieldFillQuantifier.notAllFieldsFilled.evalComputation
        (.uninstantiated :: suffix) = .holds := by
  constructor <;> rfl

/-- Every instantiated-range predicate skips an uninstantiated head without reading a cell. -/
theorem computationFillQuantifier_instantiatedRange_skipsUninstantiated
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.noFieldFilled.evalComputation
        (.uninstantiated :: suffix) =
          FieldFillQuantifier.noFieldFilled.evalComputation suffix ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        (.uninstantiated :: suffix) =
          FieldFillQuantifier.atLeastOneFieldFilled.evalComputation suffix ∧
      FieldFillQuantifier.moreThanOneFieldFilled.evalComputation
        (.uninstantiated :: suffix) =
          FieldFillQuantifier.moreThanOneFieldFilled.evalComputation suffix ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation
        (.uninstantiated :: suffix) =
          FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation suffix := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-- The mixed operator can combine an uninstantiated declared empty with a later instantiated filled slot, then ignore the suffix. -/
theorem fieldsNotCollectivelyFilled_uninstantiatedFilledPrefix_shortCircuits
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalComputation
      (.uninstantiated :: .filled :: suffix) = .holds := by
  rfl

/-- `NotExactlyOneFieldFilled` distinguishes zero, exactly one, and at least two filled slots. -/
theorem notExactlyOneFieldFilled_zeroOneTwo
    (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation [] = .holds ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation
        [.filled] = .notTrue ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation
        (.filled :: .filled :: suffix) = .holds := by
  constructor
  · rfl
  constructor <;> rfl

/-- A poison reached after only one filled slot prevents both two-filled predicates from deciding. -/
theorem secondFilledPredicates_oneFilledThenPoison_preserve
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.moreThanOneFieldFilled.evalComputation
        [.filled, .poison cause] = .poison cause ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalComputation
        (.filled :: .poison cause :: suffix) = .poison cause := by
  constructor <;> rfl

/-- A filled witness alone does not let the mixed predicate skip a poison before any declared empty witness. -/
theorem fieldsNotCollectivelyFilled_filledThenPoison_preserves
    (cause : FormalCause) (suffix : List ComputationFillSlot) :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalComputation
      (.filled :: .poison cause :: suffix) = .poison cause := by
  rfl

/-- Read order is observable: a filled decision before poison differs from the same two slots reversed. -/
theorem computationFillQuantifier_readOrderObservable
    (cause : FormalCause) :
    FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.filled, .poison cause] ≠
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.poison cause, .filled] := by
  intro impossible
  cases impossible

/-- Joining count operands preserves their order and the first cause, adding only successful counts. -/
theorem filledFieldComputationCount_append (left right : List ComputationFillSlot) :
    numberOfFilledFieldsForComputation (left ++ right) =
      (do let first ← numberOfFilledFieldsForComputation left
          let second ← numberOfFilledFieldsForComputation right
          pure (first + second)) := by
  induction left with
  | nil =>
      simp only [List.nil_append]
      cases numberOfFilledFieldsForComputation right <;>
        simp [numberOfFilledFieldsForComputation, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cons head rest ih =>
      cases head <;> simp only [List.cons_append, numberOfFilledFieldsForComputation]
      · rw [ih]
        cases numberOfFilledFieldsForComputation rest <;>
          cases numberOfFilledFieldsForComputation right <;> simp [Bind.bind, Except.bind, Functor.map, Except.map, Pure.pure, Except.pure, Nat.add_right_comm]
      · exact ih
      · exact ih
      · rfl

/-- The validation count forgets the first cause but agrees on every successful count. This
relates result domains over supplied observations, not validation and computation cell projection. -/
theorem filledFieldCount_validationProjection (cells : List CellObservation) :
    numberOfFilledFields cells =
      match numberOfFilledFieldsForComputation (cells.map CellObservation.asComputationFillSlot) with
      | .ok count => .value count
      | .error _ => .unknown := by
  induction cells with
  | nil => rfl
  | cons head rest ih =>
      cases outcome : numberOfFilledFieldsForComputation (rest.map CellObservation.asComputationFillSlot) <;>
        cases head <;>
        simp_all [numberOfFilledFields, numberOfFilledFieldsForComputation,
          CellObservation.asComputationFillSlot, Functor.map, Except.map] <;>
        split at ih <;> simp_all

/-- The actual addressed scan never invokes later payload reads after a deciding step. -/
theorem computationFillScan_deciding_prefix (kind : FieldFillQuantifier.ScanKind)
    (read : Slot → ComputationFillSlot) (first : Slot) (rest : List Slot) (seen : Bool)
    (result : FieldFillQuantifier.ScanResult)
    (decides : FieldFillQuantifier.step kind seen (read first) = .inr result) :
    FieldFillQuantifier.scanRead kind read (first :: rest) seen = .inr result := by
  simp [FieldFillQuantifier.scanRead, decides]

/-- A failed first scan prevents a composite guard from starting its other range. -/
theorem computationFillRestart_poison (operator : FieldFillQuantifier)
    (scan : FieldFillQuantifier.ScanKind → Except Error FieldFillQuantifier.ScanResult)
    (cause : FormalCause)
    (first : scan .anyFilled = .ok (.poison cause))
    (composite : operator = .notExactlyOneFieldFilled ∨ operator = .fieldsNotCollectivelyFilled) :
    operator.evalComputationUsing scan = .ok (.poison cause) := by
  rcases composite with rfl | rfl <;>
    simp [FieldFillQuantifier.evalComputationUsing, first, bind, Except.bind, pure, Except.pure]

end A12Kernel
