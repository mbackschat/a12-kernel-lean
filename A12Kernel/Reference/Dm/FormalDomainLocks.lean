import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptance
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Semantics.NumericInput

/-! # The admitted set of each scalar kind (Q2-P3)

For a decimal-valued Number placement, spec/04 §4.8 states the admitted set as a conjunction over the
read scale `r` and the rounded value `w` that the storage-regime formula derives. `admittedDecimal`
writes `r` and `w` from that formula and the effective integer-digit cap from the clause, while each
declaration's constraints come from the DM reader reading its DM-JSON body, so a derivation the clause
omits, such as the amount trait's cap, surfaces as a disagreement. Three routes are compared with the
clause: the cascade on the reader's constraints, the whole document route over a JSON-number document
through [`sampleAcceptance`](SampleAcceptance.lean), and the Kernel's codes on the retained
[formal-domain capture](../../../evidence/kernel-31.3.1/captures/q2-formal-domain-2026-11-09/MANIFEST.sha256).

The other kinds are compared through the document route against spec/06's stored-value sequence and
spec/02 §A.3's token fold. A non-default legal character set is locked in
[`SupportedCharactersLocks`](SupportedCharactersLocks.lean); the technical length gate, which spec/06
marks as resting on source reading, is outside this matrix. -/

namespace A12Kernel.Dm.FormalDomainLocks

open Lean

private def world : World := { now := { epochMillis := 0 } }

/-- A Number declaration as DM-JSON writes it; an absent member is `none`. -/
private structure NumberDecl where
  minF : Option Int := none
  maxF : Option Int := none
  positivesOnly : Bool := false
  maxInt : Option Nat := none
  amount : Bool := false
  zeroNotAllowed : Bool := false
  minLen : Option Nat := none
  maxLen : Option Nat := none
  minV : Option JsonNumber := none
  maxV : Option JsonNumber := none

private def NumberDecl.body (d : NumberDecl) : Json :=
  Json.mkObj ((d.minF.map fun v => ("minFractionalDigits", toJson v)).toList ++
    (d.maxF.map fun v => ("maxFractionalDigits", toJson v)).toList ++
    (if d.positivesOnly then [("positivesOnly", Json.bool true)] else []) ++
    (d.maxInt.map fun v => ("maxIntegerDigits", toJson v)).toList ++
    (if d.amount then [("trait", Json.str "amount")] else []) ++
    (if d.zeroNotAllowed then [("zeroNotAllowed", Json.bool true)] else []) ++
    (d.minLen.map fun v => ("minLength", toJson v)).toList ++
    (d.maxLen.map fun v => ("maxLength", toJson v)).toList ++
    (d.minV.map fun v => ("minValue", Json.num v)).toList ++
    (d.maxV.map fun v => ("maxValue", Json.num v)).toList)

/-- A one-field DM 29.8.0 model: root `Probe` holding the Number `F`. -/
private def NumberDecl.dm (d : NumberDecl) : Option DmModel :=
  let field := Json.mkObj [("type", "Field"), ("id", "/Probe/F"), ("name", "F"),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "NumberType"), ("NumberType", d.body)])])]
  let root := Json.mkObj [("type", "Group"), ("id", "/Probe"), ("name", "Probe"),
    ("Group", Json.mkObj [("repeatability", (1 : Nat)), ("elements", Json.arr #[field])])]
  let header := Json.mkObj [("id", "Dom"), ("modelType", "document"), ("modelVersion", "29.8.0"),
    ("locales", Json.arr #[Json.mkObj [("code", "en_US")]]), ("labels", Json.arr #[]),
    ("annotations", Json.arr #[]), ("modelReferences", Json.arr #[])]
  let content := Json.mkObj [
    ("modelInfo", Json.mkObj [("name", "Dom"), ("variant", "cockpit"), ("revision", "Arbeitsversion"),
      ("immutable", false)]),
    ("modelConfig", Json.mkObj [("decimalSeparator", "."), ("timeZone", "Europe/Berlin"),
      ("conditionLanguage", Json.mkObj [("code", "en_US")]), ("fieldRefByShortNameAllowed", true)]),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[root])])]
  (readModel (Json.mkObj [("header", header), ("content", content)])).toOption

private def digits (n : Nat) : Nat := (toString n).length

/-- The scale of `u · 10^-s` with its fractional trailing zeros stripped; zero has scale 0. -/
private def strippedScale (u : Int) (s : Int) : Int :=
  if u == 0 then 0 else
    let rec go (m : Nat) (s : Int) (fuel : Nat) : Int := match fuel with
      | 0 => s
      | fuel + 1 => if m % 10 == 0 then go (m / 10) (s - 1) fuel else s
    go u.natAbs s (digits u.natAbs)

/-- `|v|` rounded half up to `r` places, as an unscaled natural at scale `r`. -/
private def roundedMagnitude (v : NumericInputDecimal) (r : Nat) : Nat :=
  if (r : Int) ≥ v.scale then v.unscaled.natAbs * 10 ^ (r - v.scale).toNat
  else
    let d := 10 ^ (v.scale - r).toNat
    (v.unscaled.natAbs + d / 2) / d

/-- spec/04 §4.8's admitted-set conjunction over the storage-regime formula. A bound is compared as
authored, which equals its printed value for every bound below. -/
private def admittedDecimal (d : NumberDecl) (v : NumericInputDecimal) : Bool :=
  let minF := (d.minF.getD 0).toNat
  let maxF := d.maxF.getD 0
  let precision := digits v.unscaled.natAbs
  let r := (min (max (strippedScale v.unscaled v.scale) (max 0 (minF : Int)))
    (max 0 (15 - (precision - v.scale)))).toNat
  let q := roundedMagnitude v r
  let negative := v.unscaled < 0 && q != 0
  let w : Rat := (if negative then -1 else 1) * (q : Rat) / (10 ^ r : Nat)
  let n := digits (q / 10 ^ r)
  let cap := d.maxInt.orElse fun _ => if d.amount then some (15 - maxF).toNat else none
  let unchecked := d.minF == some (-1) && maxF == 0
  let length := (if negative then 1 else 0) + n + (if r > 0 then r + 1 else 0)
  let bound := fun (b : JsonNumber) => (b.mantissa : Rat) / (10 ^ b.exponent : Nat)
  n + r ≤ 15 && (!negative || !d.positivesOnly) &&
    (unchecked || (minF ≤ r && (r : Int) ≤ maxF)) &&
    cap.all (n ≤ ·) && (q != 0 || !d.zeroNotAllowed) &&
    d.minLen.all (· ≤ length) && d.maxLen.all (length ≤ ·) &&
    d.minV.all (bound · ≤ w) && d.maxV.all (w ≤ bound ·)

private def num (mantissa : Int) (exponent : Nat) : JsonNumber := { mantissa, exponent }

private def declarations : List NumberDecl := [
  {},
  { minF := some 2, maxF := some 2 },
  { maxF := some 2 },
  { minF := some 10, maxF := some 10 },
  { maxF := some 14 },
  { positivesOnly := true, zeroNotAllowed := true, amount := true },
  { maxInt := some 3 },
  { minF := some 2, maxF := some 2, minLen := some 5, maxLen := some 6 },
  { maxF := some 2, minV := some (num 1 0), maxV := some (num 555 2) },
  { minF := some (-1), maxF := some 0 },
  { maxF := some 2, amount := true },
  { minF := some (-1), maxF := some 0, maxV := some (num 5 0) }]

/-- `(unscaled, scale)`: zero, signs, a negative scale, trailing zeros, the fifteen-digit total, the
cap that leaves a required place no room (`123456789012345`), the amount trait's cap at scale 2
(`12345678901234` against `1234567890123`), a rounding carry into a sixteenth digit, rounding toward
and away from a bound (`5.00000000000000004`, `5.000000000000005`), and the length and value bounds. -/
private def values : List NumericInputDecimal :=
  [(0, 0), (5, 0), (-5, 0), (250, 0), (25000, 2), (1, -5), (12345, 0), (123456, 0), (999995, 3), (125, 3),
    (-1, 3), (1555, 3), (556, 2), (5555, 3), (12345678901234567, 7), (5, 1), (1000, 0), (9999, 0),
    (1234567890123456, 0), (100, 2), (-100, 2), (123456789012345, 0), (123456789012345, 2),
    (12345678901234, 0), (1234567890123, 0), (9999999999999995, 2), (9999999999999994, 2),
    (500000000000000004, 17), (5000000000000005, 15)].map fun (unscaled, scale) => { unscaled, scale }

private def field (dm : DmModel) : Option (NumField × NumericTargetConstraints) := do
  let declaration ← dm.flat.fields.head?
  let .number info := declaration.policy.kind | none
  pure (info, declaration.numericTargetConstraints)

/-- The clause agrees with the cascade on the reader's constraints for every declaration and value. -/
example : declarations.all (fun d => match d.dm.bind field with
    | none => false
    | some (info, c) => values.all fun v => admittedDecimal d v == (c.checkFormalRead info (.decimal v)).toBool) := by
  native_decide

/-- The clause agrees with the whole document route on a JSON-number document for every value of
nonnegative scale: a refused value leaves a built-in finding, an admitted one none. -/
example : declarations.all (fun d => match d.dm with
    | none => false
    | some dm => (values.filter (·.scale ≥ 0)).all fun v =>
        let doc := Json.mkObj [("Probe", Json.mkObj [("F", Json.num (num v.unscaled v.scale.toNat))])]
        (sampleAcceptance world dm doc).map (·.messageFree) == some (admittedDecimal d v)) := by
  native_decide

/-- The matrix is not vacuous: every declaration-specific row the decimal read text reaches refuses
some pair, the missing-separator row included, and some pair is admitted. -/
example : [NumericFormalReadError.totalDigitsTooLong, .negativeNotAllowed, .decimalSeparatorForbidden,
      .decimalSeparatorRequired, .fractionalDigitsOutOfRange, .integerDigitsTooLong, .zeroNotAllowed,
      .textTooShort, .textTooLong, .belowMinimum, .aboveMaximum].all (fun error =>
        declarations.any fun d => match d.dm.bind field with
          | none => false
          | some (info, c) => values.any fun v => match c.checkFormalRead info (.decimal v) with
            | .error refused => refused == error
            | .ok _ => false) &&
    declarations.any (fun d => values.any (admittedDecimal d)) := by native_decide

/-- Each retained row's Kernel code at `Probe/<field>` beside the code the reader's cascade gives the
row's JSON number, in request order. -/
private def capturedCodes (modelText requestText artifactText : String) :
    Option (List (List String × List String)) := do
  let dm ← ((parseModelJson modelText).bind (readModel ·)).toOption
  let request ← (Json.parse requestText).toOption
  let artifact ← (Json.parse artifactText).toOption
  let requested ← (request.getObjValAs? (Array Json) "rows").toOption
  let observed ← (artifact.getObjValAs? (Array Json) "rows").toOption
  requested.toList.mapM fun row => do
    let name ← (row.getObjValAs? String "name").toOption
    let .obj cells ← (row.getObjVal? "documentInline" >>= (·.getObjVal? "Probe")).toOption | none
    let lean ← cells.toList.mapM fun (fieldName, value) => do
      let .num number := value | none
      let declaration ← dm.flat.fields.find? (·.name == fieldName)
      let .number info := declaration.policy.kind | none
      let decimal : NumericInputDecimal := { unscaled := number.mantissa, scale := number.exponent }
      pure (match declaration.numericTargetConstraints.checkFormalRead info (.decimal decimal) with
        | .error error => [s!"Probe/{fieldName}:{error.errorCode}"]
        | .ok _ => [])
    let observedRow ← observed.find? fun o => (o.getObjValAs? String "name").toOption == some name
    if (observedRow.getObjValAs? Bool "enginesAgree").toOption != some true then none
    let engine ← (observedRow.getObjValAs? (Array Json) "engines").toOption >>= (·[0]?)
    let messages ← (engine.getObjValAs? (Array Json) "messages").toOption
    let kernel ← messages.toList.mapM fun message => do
      let code ← (message.getObjValAs? String "code").toOption
      let place ← (message.getObjValAs? String "field").toOption
      pure s!"{place}:{code}"
    pure (kernel, lean.flatten)

/-- On kernel 31.3.1 the missing-separator row, the amount trait's cap and the rounding carry into the
fifteen-digit total each refuse with the cascade's code, and each control is admitted. -/
example : (capturedCodes
      (include_str "../../../evidence/kernel-31.3.1/captures/q2-formal-domain-2026-11-09/Dom_DM.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2-formal-domain-2026-11-09/request.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2-formal-domain-2026-11-09/artifact.json")).map
        (·.map fun (kernel, lean) => (kernel == lean, kernel)) =
    some [(true, ["Probe/P2:zahlOhneDezimalTrenner"]), (true, []),
      (true, ["Probe/AM:zahlZuvieleVorkommastellen"]), (true, []),
      (true, ["Probe/C:stelligkeitZuLang"]), (true, [])] := by native_decide

/-- The cascade's code for one decimal on one declaration, `none` when it is admitted. -/
private def cascadeCode (d : NumberDecl) (unscaled scale : Int) : Option (Option String) := do
  let (info, c) ← d.dm.bind field
  pure (match c.checkFormalRead info (.decimal { unscaled, scale }) with
    | .error error => some error.errorCode
    | .ok _ => none)

/-- The rows a12-dmkits measured beyond the capture above when it reconciled SPEC-2026-11-09-01, on
kernel 31.3.1 with both strategies (KERNEL-FINDINGS KF681 at a12-dmkits `8b290c30b`): one required place
leaves `123456789012345` no room, fourteen integer digits pad short of two required places, and the
amount trait's cap at up to three places is twelve integer digits. -/
example : [cascadeCode { minF := some 1, maxF := some 1 } 123456789012345 0,
      cascadeCode { minF := some 2, maxF := some 2 } 12345678901234 0,
      cascadeCode { minF := some 2, maxF := some 2 } 123456789012345 2,
      cascadeCode { maxF := some 3, amount := true } 1234567890123 0,
      cascadeCode { maxF := some 3, amount := true } 123456789012 0] =
    [some (some "zahlOhneDezimalTrenner"), some (some "zahlFalscheAnzahlNachkommastellen"), some none,
      some (some "zahlZuvieleVorkommastellen"), some none] := by native_decide

/-! ## The other kinds through the document route -/

private def kindModel : DmModel :=
  let form : GroupPath := ["Form"]
  { flat := { fields := [
      { id := 1, name := "S", groupPath := form, policy.kind := .string, stringPolicy := { maxLength := some 3 } },
      { id := 2, name := "SMin", groupPath := form, policy.kind := .string,
        stringPolicy := { minLength := some 3, maxLength := some 10 } },
      { id := 3, name := "SBr", groupPath := form, policy.kind := .string,
        stringPolicy := { lineBreaksPermitted := true, maxLength := some 4 } },
      { id := 4, name := "E", groupPath := form, policy.kind := .enumeration,
        enumeration := some { storedTokens := ["A", "Z"] } },
      { id := 5, name := "B", groupPath := form, policy.kind := .boolean },
      { id := 6, name := "C", groupPath := form, policy.kind := .confirm }] }
    rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def admitted (field text : String) : Option Bool :=
  (sampleAcceptance world kindModel (Json.mkObj [("Form", Json.mkObj [(field, Json.str text)])])).map
    (·.messageFree)

/-- spec/06's sequence: the maximum and minimum lengths, both blanks, a line break where none is
permitted, a supplementary character outside the default set; where breaks are permitted, a CRLF pair
counts one unit after normalization. Enumeration membership is exact. Boolean and Confirm tokens fold
under `equalsIgnoreCase`, the long s onto `s` (spec/02 §A.3), and Confirm admits only `true`. -/
example : [("S", "abc"), ("S", "abcd"), ("S", " ab"), ("S", "ab "), ("S", "a\nb"), ("S", "😀"),
      ("SMin", "ab"), ("SMin", "abc"), ("SBr", "a\nb"), ("SBr", "ab\r\nc"), ("SBr", "ab\r\ncd"),
      ("E", "A"), ("E", "Z"), ("E", "B"), ("E", "a"),
      ("B", "true"), ("B", "false"), ("B", "TRUE"), ("B", "yes"), ("B", "falſe"), ("B", "ſ"),
      ("C", "true"), ("C", "TRUE"), ("C", "false")].map (fun (field, text) => admitted field text) =
    [some true, some false, some false, some false, some false, some false,
      some false, some true, some true, some true, some false,
      some true, some true, some false, some false,
      some true, some true, some true, some false, some true, some false,
      some true, some true, some false] := by native_decide

end A12Kernel.Dm.FormalDomainLocks
