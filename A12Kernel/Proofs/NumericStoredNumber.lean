import A12Kernel.Semantics.NumericStoredNumber

/-! # Stored Number representation laws -/

namespace A12Kernel

/-- Removing only fractional trailing zeros preserves the represented nonnegative decimal amount. -/
theorem stripFractionalZeros_preserves_amount
    (magnitude scale : Nat) :
    let stripped := StoredNumber.stripFractionalZeros magnitude scale
    (stripped.1 : Rat) / (decimalFactor stripped.2 : Nat) =
      (magnitude : Rat) / (decimalFactor scale : Nat) := by
  induction scale generalizing magnitude with
  | zero =>
      simp [StoredNumber.stripFractionalZeros]
  | succ scale ih =>
      simp only [StoredNumber.stripFractionalZeros]
      split
      · rw [ih]
        rename_i divisible
        have tenDvd : 10 ∣ magnitude :=
          Nat.dvd_of_mod_eq_zero divisible
        have scaleFraction (a b : Rat) :
            a / b = (a * 10) / (b * 10) := by
          rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
          rw [Rat.mul_assoc]
          rw [← Rat.mul_assoc (10 : Rat) (10 : Rat)⁻¹ b⁻¹]
          rw [Rat.mul_inv_cancel (10 : Rat) (by decide)]
          simp
        calc
          (↑(magnitude / 10) : Rat) /
                (decimalFactor scale : Nat) =
              ((magnitude / 10 : Nat) : Rat) * 10 /
                ((decimalFactor scale : Nat) * 10) :=
            scaleFraction _ _
          _ = (magnitude : Rat) /
                (decimalFactor (scale + 1) : Nat) := by
            have numerator :
                ((magnitude / 10 : Nat) : Rat) * 10 =
                  (magnitude : Rat) := by
              change ((magnitude / 10 : Nat) : Rat) *
                  ((10 : Nat) : Rat) = (magnitude : Rat)
              rw [← Rat.natCast_mul]
              exact congrArg (fun value : Nat => (value : Rat))
                (Nat.div_mul_cancel tenDvd)
            have denominator :
                ((decimalFactor scale : Nat) : Rat) * 10 =
                  (decimalFactor (scale + 1) : Nat) := by
              simp [decimalFactor, Nat.pow_succ]
            rw [numerator, denominator]
      · rfl

/-- Padding a nonnegative decimal coefficient with trailing zeros changes its form but not its amount. -/
theorem padFractionalScale_preserves_amount
    (magnitude naturalScale minimumScale : Nat) :
    let storedScale := max naturalScale minimumScale
    let storedMagnitude :=
      magnitude * decimalFactor (storedScale - naturalScale)
    (storedMagnitude : Rat) / (decimalFactor storedScale : Nat) =
      (magnitude : Rat) / (decimalFactor naturalScale : Nat) := by
  dsimp
  have factorIdentity :
      decimalFactor naturalScale *
          decimalFactor (max naturalScale minimumScale - naturalScale) =
        decimalFactor (max naturalScale minimumScale) := by
    rw [decimalFactor, decimalFactor, decimalFactor, ← Nat.pow_add]
    congr
    omega
  have castNat (value : Nat) :
      (value : Rat) = ((value : Int) : Rat) := by
    rfl
  rw [castNat (magnitude * decimalFactor
    (max naturalScale minimumScale - naturalScale))]
  rw [castNat (decimalFactor (max naturalScale minimumScale))]
  rw [castNat magnitude, castNat (decimalFactor naturalScale)]
  rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div]
  rw [Int.natCast_mul, ← factorIdentity, Int.natCast_mul]
  exact Rat.divInt_mul_right (Int.ofNat_ne_zero.mpr
    (Nat.ne_of_gt (Nat.pow_pos (by decide))))

/-- Store rendering never chooses fewer fractional digits than the target's declared minimum. -/
theorem storedNumber_fromComputed_minScale (amount : Rat) (minimumScale : Nat) :
    minimumScale ≤ (StoredNumber.fromComputed amount minimumScale).2.scale := by
  simp [StoredNumber.fromComputed]
  exact Nat.le_max_right _ _

/-- Stored decimal conversion preserves exactly the scale-19 `HALF_UP` amount; stripping and minimum-scale padding change only its representation. -/
theorem storedNumber_fromComputed_preserves_amount
    (amount : Rat) (minimumScale : Nat) :
    (StoredNumber.fromComputed amount minimumScale).2.amount =
      rescaleHalfUp amount decimalPreRoundScale := by
  let restoreSign := fun (sign : Int) (magnitude : Nat) =>
    if sign < 0 then -(magnitude : Int) else magnitude
  have negNatCastDiv (magnitude scale : Nat) :
      ((-(magnitude : Int) : Int) : Rat) /
          (decimalFactor scale : Nat) =
        -((magnitude : Rat) / (decimalFactor scale : Nat)) := by
    rw [Rat.intCast_neg, Rat.div_def, Rat.neg_mul]
    rfl
  have restoreSignAmountCongr
      (sign : Int)
      (leftMagnitude leftScale rightMagnitude rightScale : Nat)
      (equal :
        (leftMagnitude : Rat) / (decimalFactor leftScale : Nat) =
          (rightMagnitude : Rat) / (decimalFactor rightScale : Nat)) :
      ((restoreSign sign leftMagnitude : Int) : Rat) /
          (decimalFactor leftScale : Nat) =
        ((restoreSign sign rightMagnitude : Int) : Rat) /
          (decimalFactor rightScale : Nat) := by
    simp only [restoreSign]
    split
    · rw [negNatCastDiv, negNatCastDiv, equal]
    · exact equal
  have restoreSignNatAbs (sign : Int) :
      restoreSign sign sign.natAbs = sign := by
    simp only [restoreSign]
    split
    next negative =>
      rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt negative)]
      simp
    next nonnegative =>
      exact Int.natAbs_of_nonneg (Int.le_of_not_gt nonnegative)
  let scaled :=
    rescaleHalfUpUnscaled amount decimalPreRoundScale
  let stripped :=
    StoredNumber.stripFractionalZeros scaled.natAbs
      decimalPreRoundScale
  let storedScale := max stripped.2 minimumScale
  let storedMagnitude :=
    stripped.1 * decimalFactor (storedScale - stripped.2)
  have padded :=
    padFractionalScale_preserves_amount
      stripped.1 stripped.2 minimumScale
  have strippedAmount :=
    stripFractionalZeros_preserves_amount
      scaled.natAbs decimalPreRoundScale
  have unsignedAmount :
      (storedMagnitude : Rat) / (decimalFactor storedScale : Nat) =
        (scaled.natAbs : Rat) /
          (decimalFactor decimalPreRoundScale : Nat) :=
    padded.trans strippedAmount
  have signedAmount :=
    restoreSignAmountCongr scaled storedMagnitude storedScale
      scaled.natAbs decimalPreRoundScale unsignedAmount
  simp only [StoredNumber.fromComputed, StoredNumber.amount]
  change
    ((restoreSign scaled storedMagnitude : Int) : Rat) /
        (decimalFactor storedScale : Nat) =
      rescaleHalfUp amount decimalPreRoundScale
  rw [signedAmount, restoreSignNatAbs]
  rfl

/-- Equal numeric amount does not imply equal stored form: `7` and `7.00` remain observably different. -/
theorem equalNumericAmount_doesNotImply_equalStoredForm :
    (StoredNumber.mk 7 0).amount =
      (StoredNumber.mk 700 2).amount ∧
    StoredNumber.mk 7 0 ≠ StoredNumber.mk 700 2 := by
  simp [StoredNumber.amount, decimalFactor]
  grind

end A12Kernel
