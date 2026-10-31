import A12Kernel.Elaboration.AddressFormalLegality

/-! # The address gate's positional and staging laws

Three results carry the family. The class of a refusal is a function of the offending coordinate's
position alone, so a violation at position 0 is a serial class whatever the vector's length — the
corner that makes a repeatable root group report the serial class where the familiar reading expects
the row class. The minimum pass precedes the maximum pass over the whole vector rather than per
position, so no over-maximum class is reported while any coordinate is under the minimum. And the two
gates are staged, so a coordinate failure suppresses the sub-scope check and a group entry never
reaches it.
-/

namespace A12Kernel

/-- Position 0 is the serial position whatever the vector's length. Stated for every length because
the length-one case is the one that matters: there position 0 is also the last position, and this is
what settles the tie. -/
@[simp] theorem indexPosition_zero (length : Nat) : indexPosition 0 length = .serial := by
  simp [indexPosition]

/-- The row position requires a vector longer than one, so a length-one address can never report a
row class. This is [`indexPosition_zero`](#A12Kernel.indexPosition_zero)'s content restated as the
false generalisation it forbids. -/
theorem indexPosition_row_needs_length (position length : Nat)
    (h : indexPosition position length = .row) : 1 < length := by
  unfold indexPosition at h
  cases hp : position == 0 <;> simp only [hp, Bool.false_eq_true, ite_true, ite_false] at h
  · cases hl : position + 1 == length <;> simp only [hl] at h
    · exact absurd h (by simp)
    · have hp' : position ≠ 0 := by simpa using hp
      have hl' : position + 1 = length := by simpa using hl
      omega
  · exact absurd h (by simp)

/-- The last position of a vector longer than one is the row position, which is what makes a violated
group's own address report the row class whenever the group is not a root group. -/
theorem indexPosition_last (length : Nat) (h : 1 < length) :
    indexPosition (length - 1) length = .row := by
  unfold indexPosition
  have h0 : ¬ (length - 1 = 0) := by omega
  have h1 : length - 1 + 1 = length := by omega
  simp [h0, h1]

/-- **The root group is exactly where a violated level's own address and its descendants' agree.** At
container depth one the level is position 0 on every address, so one code covers the row and the whole
subtree; at any greater depth the row and its descendants report different codes. This is the whole
content of the correction the repeatable-root-group measurement forced. -/
theorem violatedLevelPositions_agree_iff_root (containerDepth : Nat) (h : 0 < containerDepth) :
    violatedLevelOwnPosition containerDepth = violatedLevelDescendantPosition containerDepth ↔
      containerDepth = 1 := by
  unfold violatedLevelOwnPosition violatedLevelDescendantPosition indexPosition
  cases containerDepth with
  | zero => omega
  | succ depth =>
    cases depth with
    | zero => simp
    | succ deeper => simp

/-- A violated level is the row position of its own address at depth greater than one. -/
theorem violatedLevelOwnPosition_deep (containerDepth : Nat) (h : 1 < containerDepth) :
    violatedLevelOwnPosition containerDepth = .row :=
  indexPosition_last containerDepth h

/-- A violated level is the context position of every strictly deeper address at depth greater than
one. -/
theorem violatedLevelDescendantPosition_deep (containerDepth : Nat) (h : 1 < containerDepth) :
    violatedLevelDescendantPosition containerDepth = .context := by
  obtain ⟨deeper, rfl⟩ : ∃ deeper, containerDepth = deeper + 2 := ⟨containerDepth - 2, by omega⟩
  simp [violatedLevelDescendantPosition, indexPosition]

/-- The descendant class does not depend on how deep the descendant is: every address longer than the
violated level's own gives the same answer, which is what lets one representative length stand for the
whole subtree. -/
theorem indexPosition_beyond_depth (containerDepth length : Nat) (h : containerDepth < length) :
    indexPosition (containerDepth - 1) length =
      violatedLevelDescendantPosition containerDepth := by
  match containerDepth with
  | 0 => simp [violatedLevelDescendantPosition]
  | 1 => simp [violatedLevelDescendantPosition]
  | deeper + 2 =>
      have hne : ¬ (deeper + 1 + 1 = length) := by omega
      simp [violatedLevelDescendantPosition, indexPosition, hne]

/-- No refusal exactly when the lengths agree and both passes are clear. -/
theorem indexRefusal_none_iff (indices caps : List Int) :
    indexRefusal indices caps = none ↔
      indices.length = caps.length ∧ firstBelowMinimum indices = none ∧
        firstAboveMaximum indices caps = none := by
  unfold indexRefusal
  cases hlen : indices.length != caps.length <;>
    cases hmin : firstBelowMinimum indices <;>
    cases hmax : firstAboveMaximum indices caps <;>
    simp_all

/-- A clear minimum pass means every coordinate is at least one — the readable form of the condition
above, which a consumer checks rather than the index-returning one. -/
theorem firstBelowMinimum_none_iff (indices : List Int) :
    firstBelowMinimum indices = none ↔ ∀ index ∈ indices, 1 ≤ index := by
  unfold firstBelowMinimum
  rw [List.findIdx?_eq_none_iff]
  constructor
  · intro h index hmem
    have := h index hmem
    simpa using this
  · intro h index hmem
    have := h index hmem
    simpa using this

/-- **The staging law.** While any coordinate is below the minimum, the reported class is the
under-minimum class of the *first* such position — never an over-maximum class, even when an earlier
position exceeds its cap. A consumer testing both bounds in one walk over the vector disagrees on
exactly those addresses. -/
theorem indexRefusal_minimum_precedes_maximum (indices caps : List Int) (position : Nat)
    (hlen : indices.length = caps.length)
    (hmin : firstBelowMinimum indices = some position) :
    indexRefusal indices caps = some (indexPosition position indices.length).tooSmall := by
  unfold indexRefusal
  simp [hlen, hmin]

/-- The three classes that staging law can produce, named. -/
theorem indexRefusal_belowMinimum_classes (indices caps : List Int) (position : Nat)
    (hlen : indices.length = caps.length)
    (hmin : firstBelowMinimum indices = some position) :
    indexRefusal indices caps = some .serialTooSmall ∨
      indexRefusal indices caps = some .contextTooSmall ∨
      indexRefusal indices caps = some .rowTooSmall := by
  rw [indexRefusal_minimum_precedes_maximum indices caps position hlen hmin]
  cases indexPosition position indices.length <;> simp [IndexPosition.tooSmall]

/-- **A violation at position 0 is a serial class**, on either pass and at every vector length. This
is the law the repeatable-root-group measurement confirms: the root level sits at position 0 of its
own address and of every descendant's, so one over-limit root row draws the serial class throughout
and no row or context class anywhere. -/
theorem indexRefusal_position_zero_is_serial (indices caps : List Int)
    (hlen : indices.length = caps.length)
    (h : firstBelowMinimum indices = some 0 ∨
      (firstBelowMinimum indices = none ∧ firstAboveMaximum indices caps = some 0)) :
    indexRefusal indices caps = some .serialTooSmall ∨
      indexRefusal indices caps = some .serialTooLarge := by
  unfold indexRefusal
  rcases h with hmin | ⟨hmin, hmax⟩
  · left; simp [hlen, hmin, IndexPosition.tooSmall]
  · right; simp [hlen, hmin, hmax, IndexPosition.tooLarge]

/-- **A group entry is never sub-scope-checked**, so no group address draws a sub-scope class whatever
the declaration and whatever the address supplies. -/
theorem addressRefusal_group_ignores_usb (indices caps : List Int)
    (declaredCap declaredCap' : Option Int) (supplied supplied' : UsbValue) :
    addressRefusal .group indices caps declaredCap supplied =
      addressRefusal .group indices caps declaredCap' supplied' := by
  rfl

/-- **The gates are staged.** A field's refusal that the coordinate gate does not itself report comes
from the sub-scope gate over an entirely clear vector, so a consumer that reports both is reporting one
the Kernel suppresses. -/
theorem addressRefusal_usb_implies_indices_clear (indices caps : List Int)
    (declaredCap : Option Int) (supplied : UsbValue) (refusal : AddressRefusal)
    (h : addressRefusal .field indices caps declaredCap supplied = some refusal)
    (hne : indexRefusal indices caps ≠ some refusal) :
    indexRefusal indices caps = none ∧ usbRefusal declaredCap supplied = some refusal := by
  unfold addressRefusal at h
  cases hidx : indexRefusal indices caps with
  | none => simp only [hidx] at h; exact ⟨rfl, h⟩
  | some other => simp only [hidx] at h; exact absurd (h ▸ hidx) hne

/-- **In an A12 document model the sub-scope gate has one live class.** No entity declares a cap, so
the missing and out-of-range classes cannot fire and only a supplied discriminator is refused. -/
theorem usbRefusal_a12_only_unexpected (supplied : UsbValue) (refusal : AddressRefusal)
    (h : usbRefusal a12DeclaredUsbCap supplied = some refusal) : refusal = .usbUnexpected := by
  cases supplied <;> simp [usbRefusal, a12DeclaredUsbCap] at h
  exact h.symm

/-- The unknown-name finding's address keeps only whether a sub-scope discriminator was supplied; every
coordinate becomes zero. A consumer matching findings to input cells by address therefore cannot, on
this class, and the preserved absence is the one bit it may still read. -/
theorem unknownFieldReportedAddress_zeroes (indices : List Int) (supplied : UsbValue) :
    ∀ coordinate ∈ (unknownFieldReportedAddress indices supplied).1, coordinate = 0 := by
  intro coordinate hmem
  simp only [unknownFieldReportedAddress, List.mem_map] at hmem
  obtain ⟨_, _, rfl⟩ := hmem
  rfl

end A12Kernel
