import A12Kernel.Elaboration.NumberValuesNotUnique

/-! # `FieldValuesNotUnique` conformance locks over the Number overload

The cross-scale half of the clause's typed equality is inherited rather than exhibited here: a declaration-owned reader has already produced one exact rational per present cell, so a scale-0 `5` and a scale-2 `5.00` arrive as the same atom and membership then uses the ordinary scale-19 comparison boundary.

Every case is one **ordered** scan over authored operand order, each cell tagged with whether its own operand carries a filter. The two axes the matrix separates are what enters the comparison at all, and where a filter sits relative to the duplicate.
-/

namespace A12Kernel

/-- Tag every cell of one authored operand with that operand's own filter state. -/
private def tagged (filtered : Bool) (cells : List (ValueListCell .number)) :
    List (ValueListCell .number × Bool) :=
  cells.map (·, filtered)

/-! ## What enters the comparison -/

/- Two equal present values fire the error condition; distinct values do not. -/
example :
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 5]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 6]) =
      .notFired := by
  native_decide

/- Empty cells are skipped rather than compared, so two empties are not a duplicate and one empty beside a value is not either. -/
example :
    evalValuesNotUniqueVerdict (tagged false [.empty, .empty]) = .notFired ∧
    evalValuesNotUniqueVerdict (tagged false [.present 5, .empty]) = .notFired ∧
    evalValuesNotUniqueVerdict (tagged false [.empty, .present 5, .empty]) =
      .notFired := by
  native_decide

/- A formally unavailable cell is skipped **exactly like an empty** and does not suppress: a
   duplicate on either side of it still fires. This is the correction a12-dmkits `ddaf2e13` measured
   across dynamic Groovy, generated Java, and its interpreter on both Number and Date operands. -/
example :
    evalValuesNotUniqueVerdict
        (tagged false [.present 5, .present 5, .unknown .malformed]) = .fired .value ∧
    evalValuesNotUniqueVerdict
        (tagged false [.unknown .malformed, .present 5, .present 5]) = .fired .value ∧
    evalValuesNotUniqueVerdict
        (tagged false [.present 5, .unknown .malformed, .present 5]) = .fired .value := by
  native_decide

/- Two **equal** unavailable values are what make this a skip rather than a fire-anyway: neither
   enters the comparison, so there is no duplicate to find. A suppressing account and a skipping
   account both answer "no message" here, which is why this row needs its firing siblings above to
   separate them. -/
example :
    evalValuesNotUniqueVerdict
        (tagged false [.unknown .malformed, .unknown .malformed]) = .notFired := by
  native_decide

/- A duplicate among three operands still fires, and equality is by value rather than by position. -/
example :
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 6, .present 5]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 6, .present 7]) =
      .notFired := by
  native_decide

/- A single present value can never be a duplicate, and an empty list is vacuously unique. -/
example :
    evalValuesNotUniqueVerdict (tagged false [.present 5]) = .notFired ∧
    evalValuesNotUniqueVerdict (tagged false []) = .notFired := by
  native_decide

/-! ## Firing polarity

The polarity clause is kind-generic, so it is exhibited once here rather than restated for
the token overload. -/

/- An unfiltered firing is value-typed, while a reached filter makes the same duplicate omission-typed even though both retained values are filled. -/
example :
    evalValuesNotUniqueVerdict (tagged true [.present 5, .present 5]) =
      .fired .omission ∧
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 5]) =
      .fired .value := by
  native_decide

/- The filter flag is **positional**: a filtered operand authored after the duplicate-detecting cell
   never retypes it, while one authored before does. The engine accumulates that flag while scanning
   and answers at the duplicate, so a static "some operand is filtered" test is the nearest wrong
   account and it is wrong on exactly this pair. -/
example :
    evalValuesNotUniqueVerdict
        (tagged false [.present 5, .present 5] ++ tagged true [.present 9]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict
        (tagged true [.present 9] ++ tagged false [.present 5, .present 5]) =
      .fired .omission := by
  native_decide

/- Only a cell that was actually **compared** moves the flag. A filtered operand contributing
   nothing but empties, or nothing but unavailable cells, leaves a later duplicate value-typed: mere
   specifiedness is not enough, which is the wording a12-dmkits `ddaf2e13` separated. -/
example :
    evalValuesNotUniqueVerdict
        (tagged true [.empty] ++ tagged false [.present 5, .present 5]) =
      .fired .value ∧
    evalValuesNotUniqueVerdict
        (tagged true [.unknown .malformed] ++ tagged false [.present 5, .present 5]) =
      .fired .value := by
  native_decide

/- Missing potential does not escalate an unfiltered firing: a skipped empty cell can only add a later duplicate, never remove the present one. This is the nearest wrong account, because the value-list quantifiers beside this operator do escalate on exactly that potential. -/
example :
    evalValuesNotUniqueVerdict (tagged false [.present 5, .present 5, .empty]) =
      .fired .value := by
  native_decide

/- A filter escalates a firing rather than producing one. -/
example :
    evalValuesNotUniqueVerdict (tagged true [.present 5, .present 6]) = .notFired := by
  native_decide

/-! ## The checked-document route

The clause above is only worth its measurement if the operator's own consumer reaches it. These cases run the checked operand list over an immutable checked document so the skip is locked where a real rule observes it, not only at the pure verdict.
-/

private def numberField (id : FieldId) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Form"], name,
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel :=
  { fields := [numberField 1 "A", numberField 2 "B", numberField 3 "C"] }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def threeFields? : Option (CheckedNumberValuesNotUniqueSource model) :=
  (elaborateNumberValuesNotUniqueSource model ["Form"]
    { first := .field (bare "A")
      rest := [.field (bare "B"), .field (bare "C")] }).toOption

/-- One placed nonrepeatable cell whose stored text is its own classification. -/
private def value (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw }

private def filled (field : FieldId) (number : Rat) (stored : String) :
    ClassifiedCellInput :=
  value field stored (.parsed (.num number))

/-- A present cell the declaration rejected, which is the shape the peer measured as an
    unconvertible operand. -/
private def unconvertible (field : FieldId) : ClassifiedCellInput :=
  value field "bad" (.rejected .malformed)

private def checkedVerdict? (cells : List ClassifiedCellInput) : Option Verdict := do
  let source ← threeFields?
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption
  (CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
    source document []).toOption

/- Through the checked document, an unconvertible cell is skipped on either side of the duplicate
   exactly as the pure clause says. This is the route that carries the a12-dmkits `ddaf2e13`
   correction into a rule: suppressing here would answer UNKNOWN and the rule would fail to fire one
   the kernel fires. -/
example :
    checkedVerdict? [filled 1 5 "5", filled 2 5 "5", unconvertible 3] =
      some (.fired .value) ∧
    checkedVerdict? [unconvertible 1, filled 2 5 "5", filled 3 5 "5"] =
      some (.fired .value) := by
  native_decide

/- Two equal unconvertible cells are still not a duplicate once neither enters the comparison, so
   the checked route separates the skip from a fire-anyway account just as the pure clause does. -/
example :
    checkedVerdict? [unconvertible 1, unconvertible 2] = some .notFired := by
  native_decide

/- The ordinary cases stay unchanged through the same route, so the skip is not bought by losing
   the firing itself. -/
example :
    checkedVerdict? [filled 1 5 "5", filled 2 5 "5"] = some (.fired .value) ∧
    checkedVerdict? [filled 1 5 "5", filled 2 6 "6"] = some .notFired := by
  native_decide

end A12Kernel
