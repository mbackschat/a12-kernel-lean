import A12Kernel.Reference.Dm.Document

/-! # Completeness of the Q2 sample form

Q2's question is whether some document the model accepts exists, so the sample form a12-dmkits
emits must not exclude an accepted document: an excluded field input that the reader admits must
either draw a formal error, which no accepted document carries, or be read exactly as some input
inside the form. These locks check that for one form meeting Q2-P1's constraints, over field inputs
selecting each conversion and storage-regime branch listed below for every field kind in the
`test-data-v1` profile, so a restriction is checked on a class of inputs rather than on the cases its
author recalled. They check completeness only: an over-admitting form would still pass, and whether an
emitted spelling reads as intended is replay's and the Kernel run's to settle.

The sweep is finite: the declarations and inputs below. A native number reaches the reader as its
decimal-node text, scientific below an adjusted exponent of −6 (spec/01 §2.3), so the inputs include a
native zero and a native nonzero amount past that bound; a native exponent, not representable in Lean's
`Json.num`, reaches the reader as the quoted text it converts like, such as `0E+3`. The rows follow Lean's reader where the Kernel's
reading is unmeasured (spec/01 §2.3): a field's `null` read as present-empty; a native Boolean on a
field other than a Boolean or Confirm and a native number on a non-Number field read as text; the token folds beyond ASCII case and scales past
the represented profile, which no input here reaches; a string or Boolean at a repeatable key, a document
`id` of `false`, a string, a number or a nonempty object, an undeclared member of a row other than a string and one at
the root other than a string, all read as omitted or not read at all; an object at a repeatable key
and a non-object at a fixed group's key, refused as unrepresented; and `{}` for a fixed group with no
placed field, which Lean reads as the omitted group but for one group occurrence, a fact only
over-repetition findings consult and rows within their repeatability never draw.
-/

namespace A12Kernel.Dm.SampleFormCompletenessLocks

open Lean

/-- What validation observes of one field input: the Number check's selected text and amount, or
every other kind's raw value and stored text, with a formal error as `none`. -/
private def observe (declaration : FlatFieldDecl) (json : Json) :
    Option (Option (Option (String × Rat) × RawCell × String)) := do
  let stored ← storedText? json
  let cell ← (classifyStored { fields := [declaration] } declaration
    { field := declaration.id, path := [] } stored).toOption
  match cell.raw with
  | .rejected _ => pure none
  | raw => match declaration.policy.kind with
    | .number info =>
        let input := match cell.numericDecimal with
          | some value => NumericStoredInput.decimal value
          | none => .text cell.stored
        pure (some ((declaration.numericTargetConstraints.checkFormalRead info input).toOption, raw, ""))
    | _ => pure (some (none, raw, cell.stored))

/-- Spec/04's retained leading-zero shape: one optional sign, then ASCII `0`, then any character
other than the point. -/
private def retainedLeadingZeroShape (text : String) : Bool :=
  match (match text.toList with | '+' :: rest | '-' :: rest => rest | rest => rest) with
  | '0' :: next :: _ => next != '.'
  | _ => false

/-- Q2-P1's sample form for one field's value; an absent field is an omitted key. -/
private def inForm (retained : Bool) (declaration : FlatFieldDecl) : Json → Bool
  | .str "" => true
  | .num value => match declaration.policy.kind with
    | .number _ => value.mantissa != 0 || value.exponent ≤ 6
    | _ => false
  | .bool value => match declaration.policy.kind with
    | .boolean => true
    | .confirm => value
    | _ => false
  | .str text => match declaration.policy.kind with
    | .string | .enumeration => true
    | .number _ => retained && declaration.numericTargetConstraints.leadingZerosAllowed &&
        retainedLeadingZeroShape text
    | _ => false
  | _ => false

/-- The in-form inputs that could be read as `json` is: its own decimal as a native plain number,
both Boolean tokens, the empty string and its own stored text. -/
private def candidates (json : Json) : List Json :=
  let decimal := (storedText? json).bind fun stored =>
    match convertDocumentNumber stored with
    | .decimal value =>
        let plain := value.storedNumber
        some (Json.num { mantissa := plain.unscaled, exponent := plain.scale })
    | _ => none
  decimal.toList ++ [.num 0, .bool true, .bool false, .str ""] ++ ((storedText? json).map Json.str).toList

/-- Whether an input the reader admits is excluded from the form without loss. -/
private def covered (retained : Bool) (declaration : FlatFieldDecl) (json : Json) : Bool :=
  match observe declaration json with
  | none => false
  | some none => true
  | some (some seen) => inForm retained declaration json ||
      (candidates json).any fun other =>
        inForm retained declaration other && observe declaration other == some (some seen)

private def form : GroupPath := ["Form"]

private def number (name : String) (scale : Nat) (signed : Bool)
    (constraints : NumericTargetConstraints := {}) : FlatFieldDecl :=
  { id := 1, name, groupPath := form, policy.kind := .number { scale, signed },
    numericTargetConstraints := constraints }

/-- Declarations covering each Number constraint the profile admits: scale, sign, a fixed and a
variable fractional range, the leading-zero permission with and without length bounds, the measured
`001.20` case, an integer-digit cap with value bounds, the amount trait, a forbidden zero, and the
`-1` minimum beside a zero maximum that arms no fractional check, with and without leading zeros; and
the four other kinds. Only the leading-zero permission selects a storage regime, the others decide
which inputs are formal errors. -/
private def declarations : List FlatFieldDecl := [
  number "Whole" 0 true,
  number "Unsigned" 0 false,
  number "Cents" 2 true { minFractionalDigits := 2 },
  number "Ten" 10 true { minFractionalDigits := 10 },
  number "LeadZero" 0 true { leadingZerosAllowed := true },
  number "LeadZeroCents" 2 true { minFractionalDigits := 2, leadingZerosAllowed := true },
  number "Weight" 2 true { minFractionalDigits := 2, leadingZerosAllowed := true, minStoredLength := some 6 },
  number "Range" 3 true { minFractionalDigits := 1 },
  number "Capped" 2 true
    { leadingZerosAllowed := true, maxIntegerDigits := some 2, maxStoredLength := some 5,
      minimum := some 0, maximum := some 50 },
  number "Amount" 2 false { leadingZerosAllowed := true, amount := true, zeroAllowed := false },
  number "Unchecked" 0 true { fractionalDigitsChecked := false },
  number "UncheckedLeadZero" 0 true { fractionalDigitsChecked := false, leadingZerosAllowed := true },
  { id := 1, name := "Flag", groupPath := form, policy.kind := .boolean },
  { id := 1, name := "Ack", groupPath := form, policy.kind := .confirm },
  { id := 1, name := "Text", groupPath := form, policy.kind := .string },
  { id := 1, name := "Choice", groupPath := form, policy.kind := .enumeration,
    enumeration := some { storedTokens := ["A", "B"] } }]

private def native (mantissa : Int) (exponent : Nat) : Json := .num { mantissa, exponent }

/-- Every JSON scalar kind a field key can hold, with the texts that select each reader branch:
conversion with plus, exponent, non-ASCII digits and trailing zeros, the retained leading-zero shape,
failed conversion, and Boolean and Confirm tokens in other cases. -/
private def inputs : List Json := [
  .null, .bool true, .bool false,
  native 0 0, native 0 2, native 0 10, native 1 7, native 12 0, native (-12) 0, native 12 1, native 120 2, native 12000 4,
  .str "", .str "12", .str "+12", .str "-0", .str "1.20", .str "1.2000", .str "1e1", .str "1E+3",
  .str "0e5", .str "00e1", .str "٣", .str "٠٣", .str "0012", .str "001.20", .str "+007", .str "-00",
  .str "00.5", .str "-0012", .str "abc", .str "1,5", .str "true", .str "TRUE", .str "True", .str "false",
  .str "FALSE", .str "A", .str "x", .str " 12", .str "12 ", .str "0012 ", .str "007.50", .str "0E+3", .str "0e-7"]

private def rows : GroupPath := ["Form", "Rows"]

/-- A fixed root with a String field and a repeatable group, for the form's structural exclusions. -/
private def structural : DmModel := {
  flat := {
    fields := [
      { id := 1, name := "Note", groupPath := form, policy.kind := .string },
      { id := 2, name := "Item", groupPath := rows, repeatableScope := [10], policy.kind := .string }]
    repeatableGroups := [{ level := 10, path := rows, repeatability := some 3 }] }
  rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def withForm (members : List (String × Json)) (root : List (String × Json) := []) : Json :=
  .mkObj (root ++ [("Form", .mkObj ([("Note", .str "a")] ++ members))])

/-- How the reader takes a document outside the form's structure: read exactly as the in-form
document without the excluded member, not read at all, read differently, or refused as unrepresented. -/
private inductive StructuralReading where
  | asWithout | unread | different | refused
  deriving Repr, DecidableEq

private def structuralReading (document : Json) : StructuralReading :=
  match readDocument structural document, readDocument structural (withForm []) with
  | .error _, _ => .unread
  | .ok read, .ok reference =>
      if !read.refusals.isEmpty then .refused
      else if read.data == reference.data then .asWithout else .different
  | .ok _, .error _ => .different

-- The form writes a repeatable group as an array of objects and a field's absence as an omitted key.
-- Every other value at a repeatable key reads as the omitted key or leaves the document unread, except
-- an object, which this reader refuses because its Kernel reading is unmeasured (spec/01 §2.3).
example : [("Rows", Json.null), ("Rows", .str "x"), ("Rows", .num 1), ("Rows", .bool true),
    ("Rows", .arr #[.num 1]), ("Rows", .arr #[.null]), ("Rows", .mkObj [("Item", .str "b")]),
    ("Extra", .str "x"), ("Extra", .mkObj [])].map (fun (key, value) =>
      structuralReading (withForm [(key, value)])) =
    [.asWithout, .asWithout, .asWithout, .asWithout, .unread, .unread, .refused,
      .asWithout, .asWithout] := by
  native_decide

-- An object or an array of objects at a field key reads as the omitted field (spec/01 §2.3).
example : [Json.mkObj [], .mkObj [("x", .str "y")], .arr #[], .arr #[.mkObj []]].all (fun value =>
      match readDocument structural (.mkObj [("Form", .mkObj [("Note", value)])]),
          readDocument structural (.mkObj [("Form", .mkObj [])]) with
      | .ok read, .ok omitted => read.refusals.isEmpty && read.data == omitted.data
      | _, _ => false) = true := by
  native_decide

-- An undeclared member of a row or of the root, of any kind, reads as its absence.
example :
    let row (members : List (String × Json)) : Json :=
      withForm [("Rows", .arr #[.mkObj ([("Item", .str "b")] ++ members)])]
    [Json.bool true, .null, .num 1, .arr #[], .mkObj []].all (fun value =>
      match readDocument structural (row [("X", value)]), readDocument structural (row []) with
      | .ok read, .ok without => read.refusals.isEmpty && read.data == without.data
      | _, _ => false) &&
    [Json.bool true, .num 1, .arr #[], .mkObj []].all (fun value =>
      structuralReading (withForm [] [("Other", value)]) == .asWithout) = true := by
  native_decide

-- An empty fixed group written `{}` differs from its omission by one group occurrence only.
example :
    (match readDocument structural (.mkObj [("Form", .mkObj [])]), readDocument structural (.mkObj []) with
    | .ok written, .ok omitted =>
        written.data.cells == omitted.data.cells &&
        written.data.instantiatedRows == omitted.data.instantiatedRows &&
        written.data.groupOccurrences.length == omitted.data.groupOccurrences.length + 1
    | _, _ => false) = true := by
  native_decide

-- A fixed group is an object; a scalar, `null` or array at its key is refused as unrepresented,
-- its Kernel reading unmeasured (spec/01 §2.3).
example : [Json.str "x", .null, .num 1, .bool true, .arr #[], .arr #[.mkObj []]].map
      (fun value => structuralReading (.mkObj [("Form", value)])) =
    [.refused, .refused, .refused, .refused, .refused, .refused] := by
  native_decide

-- The form writes no document-level `id`: every other `id` reads as none or leaves the document unread.
example : [Json.null, .bool true, .bool false, .str "s", .num 1, .mkObj [("x", .num 1)], .arr #[.mkObj []]].map
      (fun value => structuralReading (withForm [] [("id", value)])) =
    [.unread, .unread, .unread, .asWithout, .asWithout, .asWithout, .asWithout] := by
  native_decide

-- Without the retained leading-zero clause the form loses exactly the texts a field allowing leading
-- zeros keeps verbatim and no native number reaches, the `001.20` minimum-length case among them;
-- with it, every excluded field input draws a formal error or reads as an in-form one.
example : declarations.flatMap (fun declaration =>
      (inputs.filter fun json => !covered false declaration json).map fun json =>
        (declaration.name, json.compress)) =
    [("LeadZero", "\"0012\""), ("LeadZero", "\"-0012\""), ("LeadZeroCents", "\"001.20\""),
      ("LeadZeroCents", "\"007.50\""), ("Weight", "\"001.20\""), ("Weight", "\"007.50\""),
      ("Capped", "\"00.5\""), ("Amount", "\"0012\""), ("Amount", "\"001.20\""),
      ("Amount", "\"00.5\""), ("Amount", "\"007.50\""), ("UncheckedLeadZero", "\"0012\""),
      ("UncheckedLeadZero", "\"001.20\""), ("UncheckedLeadZero", "\"00.5\""),
      ("UncheckedLeadZero", "\"-0012\""), ("UncheckedLeadZero", "\"007.50\"")] := by
  native_decide

example : declarations.all (fun declaration => inputs.all (covered true declaration)) = true := by
  native_decide

end A12Kernel.Dm.SampleFormCompletenessLocks
