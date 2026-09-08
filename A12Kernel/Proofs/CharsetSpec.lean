import A12Kernel.Elaboration.CharsetSpec

/-! # Laws of the declared-charset gates

Four results, each about a boundary a consumer would otherwise have to discover by experiment.

`rangeShapeForcesBasicPlane` is the capsule's payoff and the one that is not visible from the source:
because a range is *three UTF-16 units with a hyphen at index 1*, and a supplementary code point
occupies two adjacent units, no arrangement of a supplementary character can leave a hyphen at that
index. So `CHARSET_CONTAINS_SURROGATES` is structurally unreachable for a range entry, and a consumer
need only run the surrogate test on the other two shapes.

`stagesShadow` and its converse pin the parse/validate split: a charset with any parse-stage refusal
reports exactly those and a parsing one reports none of them, so the six classes are never all live.

`charsetParseError_is_exactly_the_empty_entry` settles what a class named for a general parse failure
actually catches, and `tooLong_only_for_combined` bounds the other validate class the same way
`rangeShapeForcesBasicPlane` bounds the surrogate one.

**Not claimed:** nothing here says the Kernel *reports* these lists in this order, only that the
refusals it computes stand in these relations. Order across entries is the list's, and this project
has no external observation of a charset refusal at all.
-/

namespace A12Kernel

/-- Every code point contributes at least one unit. -/
private theorem length_le_utf16UnitsOf (l : List Char) : l.length ≤ (utf16UnitsOf l).length := by
  induction l with
  | nil => simp [utf16UnitsOf]
  | cons c cs ih =>
      simp only [utf16UnitsOf, List.length_cons, List.length_append]
      split <;> simp <;> omega

/-- …and at most two. -/
private theorem utf16UnitsOf_le_two_mul (l : List Char) :
    (utf16UnitsOf l).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [utf16UnitsOf]
  | cons c cs ih =>
      simp only [utf16UnitsOf, List.length_cons, List.length_append]
      split <;> simp <;> omega

/-- A Lean `Char` is a Unicode scalar value, so it is never itself a surrogate. The whole
basic-plane case rests on this and on nothing about A12. -/
private theorem char_not_surrogate (c : Char) : c.toNat < 0xD800 ∨ 0xDFFF < c.toNat := by
  have hv := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at hv
  simp only [Char.toNat]
  omega

/-- **Three units with a hyphen at index 1 forces three basic-plane code points.** A supplementary
code point occupies two *adjacent* units, so in a three-unit list either placement lands one half of
that pair at index 1, where the hyphen has to be. -/
private theorem no_surrogate_of_three_units_with_hyphen (l : List Char)
    (hlen : (utf16UnitsOf l).length = 3) (hmid : (utf16UnitsOf l)[1]? = some 0x2D) :
    ∀ u ∈ utf16UnitsOf l, u < 0xD800 ∨ 0xDFFF < u := by
  have hle := length_le_utf16UnitsOf l
  have hge := utf16UnitsOf_le_two_mul l
  match l with
  | [] => simp [utf16UnitsOf] at hlen
  | [_] => simp [utf16UnitsOf] at hle hge hlen; omega
  | [a, b] =>
      by_cases ha : a.val < 0x10000 <;> by_cases hb : b.val < 0x10000 <;>
        simp [utf16UnitsOf, ha, hb] at hlen hmid ⊢ <;> omega
  | [a, b, c] =>
      by_cases ha : a.val < 0x10000 <;> by_cases hb : b.val < 0x10000 <;>
        by_cases hc : c.val < 0x10000 <;> simp [utf16UnitsOf, ha, hb, hc] at hlen ⊢
      exact ⟨char_not_surrogate a, char_not_surrogate b, char_not_surrogate c⟩
  | _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at hle; omega

/-- **The surrogate class is unreachable for a range entry**, so a consumer may skip that test on the
range shape entirely. -/
theorem rangeShapeForcesBasicPlane (s : String) (h : isRangeDefinition s = true) :
    containsSurrogates s = false := by
  simp only [isRangeDefinition, Bool.and_eq_true, beq_iff_eq, utf16Length, utf16Units,
    maxGraphemeLength] at h
  have hall := no_surrogate_of_three_units_with_hyphen s.toList h.1 h.2
  simp only [containsSurrogates, utf16Units, List.any_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, not_and]
  intro u hu hlo
  have := hall u hu
  omega

/-- The three shape tests cover every nonempty entry between them. -/
private theorem shapeOf_ne_unparsable_of_ne_empty (s : String) (h : s ≠ "") :
    shapeOf s ≠ .unparsable := by
  simp only [shapeOf]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i hc ha
        exact absurd (by simp [isCombinedGrapheme, ha, h]) hc

/-- Only the empty entry reaches the catch-all shape. -/
private theorem shapeOf_unparsable_imp_empty (s : String) (h : shapeOf s = .unparsable) :
    s = "" := by
  by_cases hEmpty : s = ""
  · exact hEmpty
  · exact absurd h (shapeOf_ne_unparsable_of_ne_empty s hEmpty)

/-- **`CHARSET_PARSE_ERROR` fires on exactly the empty entry.** Its name promises a general parse
failure; its trigger is a single shape, because the other three tests are jointly exhaustive over
nonempty strings. -/
theorem charsetParseError_is_exactly_the_empty_entry (e : CharsetEntry) :
    parseRefusal e = some .charsetParseError ↔ e.text = "" := by
  constructor
  · intro h
    simp only [parseRefusal] at h
    cases hs : shapeOf e.text with
    | range => rw [hs] at h; simp only at h; split at h <;> simp_all
    | combined => rw [hs] at h; simp only at h; split at h <;> simp_all
    | atomic => rw [hs] at h; simp at h
    | unparsable => exact shapeOf_unparsable_imp_empty e.text hs
  · intro h
    have hshape : shapeOf e.text = .unparsable := by rw [h]; rfl
    simp [parseRefusal, hshape]

/-- **The too-long class is a combined grapheme's alone.** A range is exactly the maximum length and
an atomic entry exactly one unit, so neither can exceed the bound the test compares against. -/
theorem tooLong_only_for_combined (e : CharsetEntry)
    (h : maxGraphemeLength < utf16Length e.text) : shapeOf e.text = .combined := by
  have hne : e.text ≠ "" := by
    intro hEq
    rw [hEq] at h
    simp only [maxGraphemeLength, show utf16Length "" = 0 from rfl] at h
    omega
  simp only [shapeOf]
  split
  · rename_i hr
    simp only [isRangeDefinition, Bool.and_eq_true, beq_iff_eq] at hr
    omega
  · split
    · rfl
    · rename_i hc
      split
      · rename_i ha
        simp only [isAtomicGrapheme, beq_iff_eq] at ha
        simp only [maxGraphemeLength] at h
        omega
      · rename_i ha
        exact absurd (by simp [isCombinedGrapheme, ha, hne]) hc

/-- **The two stages shadow**: a charset with any parse-stage refusal reports exactly those. -/
theorem stagesShadow (charset : List CharsetEntry) (h : parseRefusals charset ≠ []) :
    charsetRefusals charset = parseRefusals charset := by
  have hne : (parseRefusals charset).isEmpty = false := by
    cases hr : parseRefusals charset with
    | nil => exact absurd hr h
    | cons _ _ => rfl
  simp [charsetRefusals, parseCharset, hne]

/-- Its other side: a parsing charset reports **only** validate-stage classes, so the two sets are
disjoint across every charset rather than merely usually. -/
theorem parsingCharsetReportsNoParseClass (charset : List CharsetEntry)
    (h : parseRefusals charset = []) :
    charsetRefusals charset =
      charset.flatMap validateEntryRefusals ++
        overlapRefusals charset ((parseCharset charset).getD ⟨[], []⟩) := by
  have hempty : (parseRefusals charset).isEmpty = true := by rw [h]; rfl
  simp [charsetRefusals, parseCharset, hempty]

end A12Kernel
