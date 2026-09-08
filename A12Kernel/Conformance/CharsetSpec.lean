import A12Kernel.Elaboration.CharsetSpec

/-! # Locks on the declared-charset gates

`external evidence pending`: the account is read from the Kernel's charset utility, and no probe here
authors a restricted charset. These cases lock *this project's* chosen reading so a later calibration
has something exact to disagree with.

The matrix separates the shape cascade's order, each parse class against an admitted control differing
in one axis, the surrogate entry's passage through the parse stage into the validate one, both validate
classes together on a single entry, the stage shadowing, and the overlap gate against two controls that
each remove exactly one of its two conditions.

Every fixture is built from explicit code points rather than from literal accented characters, because
a combining sequence and its precomposed form look identical in a source file and measure differently —
which is precisely the distinction these cases turn on.
-/

namespace A12Kernel.Conformance.CharsetSpec

open A12Kernel

/-- One code point as a string, so no fixture depends on how an editor normalises the file. -/
private def cp (n : Nat) : String := String.singleton (Char.ofNat n)

/-- COMBINING ACUTE ACCENT — one code point that composes with the one before it. -/
private def acute : String := cp 0x0301

private def eAcute : String := "e" ++ acute
private def oAcute : String := "o" ++ acute
private def xAcute : String := "x" ++ acute

/-- MATHEMATICAL DOUBLE-STRUCK SMALL A — a supplementary-plane code point, so two UTF-16 units. -/
private def mathA : String := cp 0x1D552

private def E (t : String) (cs : List String) : CharsetEntry := ⟨t, cs⟩

private def codes (charset : List CharsetEntry) : List String :=
  (charsetRefusals charset).map KernelStaticDiagnostic.kernelCode

/- **The shape cascade, including the order that matters.** `a-c` is a range and not a
three-character grapheme, because the range test runs first over the same three units. -/
example :
    shapeOf "a-c" = .range ∧ shapeOf "a" = .atomic ∧ shapeOf eAcute = .combined ∧
      shapeOf "" = .unparsable := by
  native_decide

/- **A charset holding one of each admitted shape is clean**, which is the control every refusing row
below differs from in one axis. -/
example : codes [E "a-c" ["a", "-", "c"], E "a" ["a"], E eAcute [eAcute]] = [] := by
  native_decide

/- **The range gate both ways.** Reversing the endpoints of the admitted range above is the only
change. -/
example :
    codes [E "c-a" ["c", "-", "a"]] = ["CHARSET_RANGE_START_AFTER_END"] ∧
      codes [E "a-c" ["a", "-", "c"]] = [] := by
  native_decide

/- **The cluster test is what forbids a digraph.** `ch` decomposes into as many clusters as it has
units, so it combines nothing; the accented pair has the same unit count and one cluster fewer, and is
admitted. -/
example :
    codes [E "ch" ["c", "h"]] = ["CHARSET_GRAPHEME_CLUSTER_EQUALS_LENGTH"] ∧
      codes [E eAcute [eAcute]] = [] := by
  native_decide

/- **The catch-all fires on the empty entry**, which
`charsetParseError_is_exactly_the_empty_entry` proves is its only trigger. -/
example : codes [E "" []] = ["CHARSET_PARSE_ERROR"] := by
  native_decide

/- **The surrogate trap.** A supplementary code point is not one UTF-16 unit, so it is read as a
combined grapheme, *passes* the parse stage on its cluster count, and is caught only by validate. A
consumer measuring length in code points admits it outright and never reaches the class. -/
example :
    parseRefusal (E mathA [mathA]) = none ∧
      codes [E mathA [mathA]] = ["CHARSET_CONTAINS_SURROGATES"] := by
  native_decide

/- **A range entry never reports the surrogate class**, which
`rangeShapeForcesBasicPlane` proves for every range rather than for this one. -/
example : containsSurrogates "a-c" = false ∧ isRangeDefinition "a-c" = true := by
  native_decide

/- **Both validate classes on one entry, in stage order.** The supplementary code point supplies the
surrogate and the four units the excess length; neither suppresses the other. -/
example :
    codes [E (mathA ++ eAcute) [mathA, eAcute]] =
      ["CHARSET_CONTAINS_SURROGATES", "CHARSET_GRAPHEME_TOO_LONG"] := by
  native_decide

/- **The length bound alone**, with no surrogate: four units in two clusters parses and then exceeds
the maximum, where the three-unit entry beside it does not. -/
example :
    codes [E (eAcute ++ xAcute) [eAcute, xAcute]] = ["CHARSET_GRAPHEME_TOO_LONG"] ∧
      codes [E ("a" ++ eAcute) ["a", eAcute]] = [] := by
  native_decide

/- **The stages shadow.** One backwards range in the charset suppresses the surrogate report the same
entry draws on its own — the validate stage never runs. -/
example :
    codes [E "c-a" ["c", "-", "a"], E mathA [mathA]] = ["CHARSET_RANGE_START_AFTER_END"] := by
  native_decide

/- **The overlap gate, and each of its two conditions removed in turn.** The offending entry is a
leading `a` followed by an accented cluster; the partner begins with that same accented cluster and
runs one unit longer. Dropping the standalone `a` removes the *leading clusters already present*
condition, and replacing the partner's first cluster removes the *suffix begins another grapheme* one.
Each control silences the refusal on its own, so neither condition is doing the other's work. -/
example :
    codes [E "a" ["a"], E ("a" ++ eAcute) ["a", eAcute], E (eAcute ++ "b") [eAcute, "b"]] =
        ["CHARSET_GRAPHEME_OVERLAP"] ∧
      codes [E ("a" ++ eAcute) ["a", eAcute], E (eAcute ++ "b") [eAcute, "b"]] = [] ∧
      codes [E "a" ["a"], E ("a" ++ eAcute) ["a", eAcute], E (oAcute ++ "b") [oAcute, "b"]] = [] := by
  native_decide

/- **Its third condition: a partner of the suffix's own length is not an overlap.** Putting the
accented cluster in the charset as an entry of its own gives the offending entry a partner that both
begins with its suffix and equals it, which simplification would collapse rather than refuse. Without
the length test this row reports an overlap that the Kernel does not. -/
example : codes [E "a" ["a"], E eAcute [eAcute], E ("a" ++ eAcute) ["a", eAcute]] = [] := by
  native_decide

end A12Kernel.Conformance.CharsetSpec
