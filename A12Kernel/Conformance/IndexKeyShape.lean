import A12Kernel.Elaboration.IndexKeyShape

/-! # Locks on a constant index key's fit

Verdicts are read through the admission cascade's key-agreement stage so
the empty key meets its own disjunct: `true` is an admitted key and `false` the
`MVK_INDEX_VALUE_INVALID` refusal. The rows are the peer's
`CheckerIndexKeyConstantAgreementTest`, one per discriminating shape of each kind
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26-index-key-shape)), and its
`IndexKeyNormalizationPopulation` line-terminator rows
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-key-dialect)).
Additional UTF-16, padding and Number-shape locks are source-backed separators, not new measured
evidence.

The String patterns are injected, so each fixture's matcher is a hand-written stand-in for its Java
pattern. Those rows lock that the fit asks the length and the pattern together over the collapsed
whole key, not the pattern dialect.
-/

namespace A12Kernel.Conformance.IndexKeyShape

open A12Kernel

private def field (kind : FieldKind) : FlatFieldDecl :=
  { id := 1, groupPath := ["Policy", "Items"], name := "K", policy := { kind }
    repeatableScope := [10] }

private def text (policy : StringFieldPolicy := {}) (pattern : Option String := none) :
    FlatFieldDecl :=
  { field .string with stringPolicy := policy, stringPatternSource := pattern }

private def custom (minimum maximum : Option Nat := none) : FlatFieldDecl :=
  { field .string with customType := some { name := "Code", minLength := minimum, maxLength := maximum } }

private def number (minFraction maxFraction : Nat) (maxInteger : Option Nat := none) :
    FlatFieldDecl :=
  { field (.number { scale := maxFraction, signed := true }) with
    numericTargetConstraints :=
      { minFractionalDigits := minFraction, maxIntegerDigits := maxInteger } }

/-- The fit reads a temporal field's format alone, so one component set serves every format. -/
private def temporal (format : String) : FlatFieldDecl :=
  { field (.temporal .date TemporalComponents.fullDate) with
    temporalTargetPolicy := some { format } }

private def admitted (indexField : FlatFieldDecl) (key : String)
    (matcher : String → Bool := fun _ => true) : Option Bool :=
  (SemanticIndexAdmissionKey.constantFor? indexField matcher key).map
    fun admissionKey => (keyAgreementRefusal admissionKey).isNone

private def upper (character : Char) : Bool := 'A' ≤ character && character ≤ 'Z'

/-- `[A-Z]{2}[0-9]` -/
private def twoLettersDigit (key : String) : Bool :=
  match key.toList with
  | [a, b, c] => upper a && upper b && c.isDigit
  | _ => false

/-- `[A-Z]+` -/
private def capitals (key : String) : Bool := !key.isEmpty && key.toList.all upper

/-- `[^0-9]{2}` -/
private def twoNonDigits (key : String) : Bool :=
  key.length == 2 && key.toList.all (!·.isDigit)

/- String: any constant, the empty one by the cascade's own disjunct, length bounds on both sides,
   the pattern over the whole key, pattern and length each refusing alone, and a supplementary
   character counted as one. The key fit is all these lock: the Kernel also refuses both
   supplementary-character conditions with a codeless unsupported-character finding, which belongs
   to the condition text and not to the key (peer `CODELESS_ROWS`). -/
example :
    [admitted (text) "ANY", admitted (text) "",
      admitted (text { minLength := some 2, maxLength := some 3 }) "AB",
      admitted (text { minLength := some 2, maxLength := some 3 }) "ABCD",
      admitted (text { minLength := some 2, maxLength := some 3 }) "A",
      admitted (text (pattern := some "[A-Z]{2}[0-9]")) "AB1" twoLettersDigit,
      admitted (text (pattern := some "[A-Z]{2}[0-9]")) "XAB1" twoLettersDigit,
      admitted (text { maxLength := some 3 } (some "[A-Z]+")) "AB" capitals,
      admitted (text { maxLength := some 3 } (some "[A-Z]+")) "ABCD" capitals,
      admitted (text { maxLength := some 3 } (some "[A-Z]+")) "ab" capitals,
      admitted (text (pattern := some "[^0-9]{2}")) "😀" twoNonDigits,
      admitted (text (pattern := some "[^0-9]{2}")) "😀a" twoNonDigits] =
    [some true, some false, some true, some false, some false, some true, some false,
      some true, some false, some false, some false, some true] := by
  native_decide

/- Line terminators reach both checks with CRLF collapsed and a lone CR kept, on fields permitting
   no line break. The keys are `a` + LF, `a` + CR and `a` + CRLF. Without the collapse the CRLF key
   would pass the minimum and fail the `a\n` pattern. -/
example :
    let keys := ["a\n", "a\r", "a\r\n"]
    let pattern (expected : String) : FlatFieldDecl := text (pattern := some expected)
    [keys.map (admitted (pattern "a\\n") · (· == "a\n")),
      keys.map (admitted (pattern "a\\r") · (· == "a\r")),
      keys.map (admitted (pattern "a\\r\\n") · (· == "a\r\n")),
      keys.map (admitted (text { maxLength := some 2 }) ·),
      keys.map (admitted (text { minLength := some 3 }) ·)] =
    [[some true, some false, some true], [some false, some true, some false],
      [some false, some false, some false], [some true, some true, some true],
      [some false, some false, some false]] := by
  native_decide

example :
    [admitted (custom) "A", admitted (custom (some 0) (some 0)) "A",
      admitted (custom (some 4)) "A\r\r\nB",
      admitted (custom (some 4)) "A\r\nB",
      admitted (custom none (some 3)) "A\r\r\nB",
      admitted (custom none (some 3)) "A\r\nB",
      admitted (custom none (some 4)) "A\r\r\nB"] =
    [some true, some true, some true, some false, some false, some true, some true] := by
  native_decide

-- Custom key shape uses the custom declaration's bounds, bypassing ordinary String policy;
-- KF542 measures its independent custom length profile.
example :
    let declaration := { custom (some 4) (some 4) with
      stringPolicy := { minLength := some 5, maxLength := some 5 }
      stringPatternSource := some "[A-Z]+" }
    [admitted declaration "A\r\r\nB" (fun _ => false),
      admitted declaration "ABC" (fun _ => true),
      admitted declaration "ABCDE" (fun _ => true)] =
    [some true, some false, some false] := by
  native_decide

-- Source-backed length locks exercise UTF-16 counting separately from the whole-key matcher.
-- These direct keys make no claim about the condition reader's character repertoire.
example :
    [admitted (text { minLength := some 2, maxLength := some 2 }) "😀",
      admitted (text { maxLength := some 1 }) "😀",
      admitted (text { maxLength := some 2 } (some "[^0-9]{2}")) "😀a" twoNonDigits,
      admitted (text { maxLength := some 3 } (some "[^0-9]{2}")) "😀a" twoNonDigits,
      admitted (custom (some 2) (some 2)) "😀",
      admitted (custom none (some 1)) "😀",
      admitted (custom (some 3)) "😀"] =
    [some true, some false, some false, some true, some true, some false, some false] := by
  native_decide

example :
    [admitted (text { minLength := some 2, maxLength := some 2 }) " A",
      admitted (text { maxLength := some 1 }) " A",
      admitted (text { minLength := some 2 }) "é",
      admitted (text { maxLength := some 1 }) "é",
      admitted (custom (some 2) (some 2)) " A",
      admitted (custom none (some 1)) " A",
      admitted (custom (some 2)) "é",
      admitted (custom none (some 1)) "é"] =
    [some true, some false, some false, some true, some true, some false, some false, some true] := by
  native_decide

/- Number: the fraction's digit count against the declared bounds after `.` or `,`, the integer
   digits unasked even against a declared maximum of two, a minus admitted and a plus refused. -/
example :
    [["5", "-5", "05", "5.0", "+5", "x"].map (admitted (number 0 0) ·),
      ["5", "5.5", "5,55", "5.555"].map (admitted (number 0 2) ·),
      ["5", "5.00", "5,00", "5.0"].map (admitted (number 2 2) ·),
      ["12345"].map (admitted (number 0 0 (some 2)) ·)] =
    [[some true, some true, some true, some false, some false, some false],
      [some true, some true, some true, some false],
      [some false, some true, some true, some false],
      [some true]] := by
  native_decide

-- Source-backed Number shapes ask the ASCII fraction pattern alone, even for unsigned fields
-- with zero and leading zeros forbidden in stored values (spec/08 §4).
example :
    let unsigned := { number 0 2 (some 1) with
      policy := { kind := .number { scale := 2, signed := false } }
      numericTargetConstraints := {
        minFractionalDigits := 0, maxIntegerDigits := some 1,
        zeroAllowed := false, leadingZerosAllowed := false } }
    ["-0", "-0.00", "00", "000.0", "-0.000", "+0", " 0", "0 ", "٠", "0.٠"].map
        (admitted unsigned ·) =
      [some true, some true, some true, some true, some false, some false, some false,
        some false, some false, some false] := by
  native_decide

/- Boolean and Confirm: the literal words alone, case-sensitively. A Boolean with the custom
   values `J` and `N` still admits `true` and refuses `J`; this model carries no custom values, and
   the rows show it needs none. -/
example :
    ["true", "false", "yes", "TRUE", "J"].map (admitted (field .boolean) ·) =
      [some true, some true, some false, some false, some false] ∧
    ["true", "false"].map (admitted (field .confirm) ·) = [some true, some false] := by
  native_decide

/- Temporal: one digit per component letter, so a day that is no calendar day fits, while another
   order, a short component or a missing part does not; a quoted `T` is literal. -/
example :
    ["2020-01-31", "2020-13-45", "31.01.2020", "2020-1-31"].map
        (admitted (temporal "yyyy-MM-dd") ·) =
      [some true, some true, some false, some false] ∧
    ["31.01.2020", "31-01-2020"].map (admitted (temporal "dd.MM.yyyy") ·) =
      [some true, some false] ∧
    ["2020-01-31T10:15:00", "2020-01-31"].map (admitted (temporal "yyyy-MM-dd'T'HH:mm:ss") ·) =
      [some true, some false] ∧
    ["10:15:00", "10:15"].map (admitted (temporal "HH:mm:ss") ·) = [some true, some false] ∧
    ["2020-01", "01.2020"].map (admitted (temporal "yyyy-MM") ·) = [some true, some false] := by
  native_decide

/- A date range is two dates around its separator; one date alone does not fit. -/
example :
    let periods : FlatFieldDecl :=
      { field .dateRange with dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }
    ["01.01.2020-31.01.2020", "01.01.2020"].map (admitted periods ·) = [some true, some false] := by
  native_decide

/- An Enumeration key is a stored token exactly, case-sensitively
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-literal-key)); a declaration lacking the
   policy its kind needs answers nothing rather than a guess. -/
example :
    let tiers : FlatFieldDecl :=
      { field .enumeration with enumeration := some { storedTokens := ["A1", "B2"] } }
    ["A1", "a1"].map (admitted tiers ·) = [some true, some false] ∧
    admitted (field .enumeration) "A1" = none ∧
    admitted (field (.temporal .date TemporalComponents.fullDate)) "2020-01-31" = none := by
  native_decide

end A12Kernel.Conformance.IndexKeyShape
