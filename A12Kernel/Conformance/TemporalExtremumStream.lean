import A12Kernel.Elaboration.TemporalExtremumStream

/-! # A12Kernel.Conformance.TemporalExtremumStream — the extrema's complete-Date fold, read from a model

The fold was reachable only from a hand-built stream, so every earlier row about it assumed the
projection these rows now exercise. What is worth locking here is the Date family's own empty rule
and its two failure modes, because each has a plausible wrong account that a single happy-path row
would leave standing: an unspecified operand could contribute a synthetic value the way an empty
Number contributes zero, a malformed one could be skipped like an absent one, and a formally
unavailable one could be skipped rather than aborting.
-/

namespace A12Kernel.Conformance.TemporalExtremumStream

open A12Kernel

private def dateField (id : Nat) (name : String)
    (components : TemporalComponents := TemporalComponents.fullDate)
    (format : String := "yyyy-MM-dd") : FlatFieldDecl :=
  { id, groupPath := ["Probe"], name,
    policy := { kind := .temporal .date components },
    temporalTargetPolicy := some { format } }

/-- Year and month only: the same family, a component-omitting format. -/
private def yearMonth : TemporalComponents where
  year := true
  month := true
  day := false
  hour := false
  minute := false
  second := false

private def probeModel : FlatModel :=
  { fields := [
      dateField 1 "A",
      dateField 2 "B",
      dateField 3 "C",
      -- Admitted as an operand list, declined by the fold.
      dateField 4 "Month" yearMonth "yyyy-MM",
      dateField 5 "Month2" yearMonth "yyyy-MM",
      { id := 6, groupPath := ["Probe", "Rows"], name := "RowDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" },
        repeatableScope := [20] }]
    repeatableGroups := [{ level := 20, path := ["Probe", "Rows"] }] }

example : probeModel.validate.isOk = true := by native_decide

private def fieldOperand (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Probe"], field := name }

private def sourceOf : List SurfaceFieldEntityOperand → SurfaceFieldEntitySource
  | [] => { first := fieldOperand "A", rest := [] }
  | first :: rest => { first, rest }

private def admitted? (names : List String) :
    Option (CheckedTemporalExtremumOperands probeModel) :=
  (TemporalExtremumOperands.elaborate probeModel ["Probe"]
    (sourceOf (names.map fieldOperand))).toOption

/-- The exact instant is irrelevant to this fold, which orders the decoded parts; it is fixed so a
    row cannot pass by accident of the epoch value. -/
private def dateValue (year month day : Nat) : DateValue where
  instant := { epochMillis := 0 }
  parts := { year, month, day }
  basis := .storedGregorian

private def dateCell (year month day : Nat) : RawCell :=
  .parsed (.temporal (.date (dateValue year month day)))

/-- Field ids read their own entry; anything unlisted is absent. -/
private def raw (cells : List (FieldId × RawCell)) : RawFlatContext where
  read id :=
    match cells.find? fun entry => entry.1 == id with
    | some entry => entry.2
    | none => .empty

private def foldOf (names : List String) (op : TemporalExtremumOp)
    (cells : List (FieldId × RawCell)) :
    Option (SimpleComparisonOperand FullDate) := do
  let checked ← admitted? names
  (TemporalExtremumStream.eval checked op
    (probeModel.checkContext (raw cells)) .validation).toOption

private def ymd (year month day : Nat) : Option FullDate :=
  FullDate.ofYmd? year month day

/-! ## The selection itself, and that it is chronological rather than authored -/

example : foldOf ["A", "B"] .maximum [(1, dateCell 2024 3 5), (2, dateCell 2024 7 1)] =
    ((ymd 2024 7 1).map fun date => .value date true) := by
  native_decide

example : foldOf ["A", "B"] .minimum [(1, dateCell 2024 3 5), (2, dateCell 2024 7 1)] =
    ((ymd 2024 3 5).map fun date => .value date true) := by
  native_decide

/- The later date authored **first**: the answer is unchanged, so the fold reads the values and not
   the operand order. Without this row a fold returning its first operand would pass both rows
   above. -/
example : foldOf ["A", "B"] .maximum [(1, dateCell 2024 7 1), (2, dateCell 2024 3 5)] =
    ((ymd 2024 7 1).map fun date => .value date true) := by
  native_decide

/-! ## The Date family's empty rule, which is not the Number family's

An unspecified operand does not compete and contributes no synthetic value; it only records that
the selection was incomplete. An **all**-empty list yields no value at all rather than a zero or an
epoch date. -/

example : foldOf ["A", "B"] .maximum [(1, dateCell 2024 3 5)] =
    ((ymd 2024 3 5).map fun date => .value date false) := by
  native_decide

example : foldOf ["A", "B"] .maximum [] = some .notEvaluated := by native_decide

/- The same two operands both filled: `given` flips to true, so the flag above tracks the absent
   operand rather than being constant. -/
example : foldOf ["A", "B"] .maximum
    [(1, dateCell 2024 3 5), (2, dateCell 2024 1 1)] =
    ((ymd 2024 3 5).map fun date => .value date true) := by
  native_decide

/-! ## The two failure modes, told apart from absence

A formally invalid operand aborts the whole fold rather than being skipped — including when a value
has already been selected, which is the case a left-to-right implementation gets wrong. A payload of
the wrong kind is malformed rather than absent, so a broken cell can never read as an unspecified
one. -/

example : foldOf ["A", "B"] .maximum
    [(1, dateCell 2024 3 5), (2, .rejected .dateFormat)] =
    some (.unknown .dateFormat) := by
  native_decide

/- Reversed, so the abort is not merely "the last operand decides". -/
example : foldOf ["A", "B"] .maximum
    [(1, .rejected .dateFormat), (2, dateCell 2024 3 5)] =
    some (.unknown .dateFormat) := by
  native_decide

example : foldOf ["A", "B"] .maximum
    [(1, dateCell 2024 3 5), (2, .parsed (.str "2024-07-01"))] =
    some (.unknown .malformed) := by
  native_decide

/- The absent control beside them: the same position, unfilled, is a value with incomplete
   provenance rather than UNKNOWN, which is what makes the two rows above about the cell and not
   about the operand slot. -/
example : foldOf ["A", "B"] .maximum [(1, dateCell 2024 3 5), (2, .empty)] =
    ((ymd 2024 3 5).map fun date => .value date false) := by
  native_decide

/-! ## What this slice declines, and why each is a boundary rather than a verdict -/

private def refusal? (names : List String) :
    Option TemporalExtremumStreamError := do
  let checked ← admitted? names
  match TemporalExtremumStream.eval checked .maximum
      (probeModel.checkContext (raw [])) .validation with
  | .ok _ => none
  | .error error => some error

/- A component-omitting list is **admitted as an operand list** and declined by the fold, which is
   the split this capsule rests on: admission is measured, the ordering of such values is not. -/
example : (admitted? ["Month", "Month2"]).isSome = true := by native_decide

example : refusal? ["Month", "Month2"] = some (.notCompleteDate yearMonth) := by
  native_decide

/- Neither decline claims a Kernel class, because the Kernel admits both shapes. -/
example : (refusal? ["Month", "Month2"]).bind
    TemporalExtremumStreamError.diagnostic? = none := by
  native_decide

private def starGroups : List SurfaceStarGroupSegment :=
  [{ name := "Probe" }, { name := "Rows", starred := true }]

private def starOperand : SurfaceFieldEntityOperand :=
  .star { base := .absolute, groups := starGroups, field := "RowDate" }

/- A starred operand: admitted by the operand list, declined here because it resolves through the
   addressed context. Folding only its declaring cell would answer for one row where the Kernel
   folds every one, which is worse than declining. -/
private def starChecked? : Option (CheckedTemporalExtremumOperands probeModel) :=
  (TemporalExtremumOperands.elaborate probeModel ["Probe"]
    { first := starOperand, rest := [] }).toOption

/- Admitted by the operand list — a lone star is a complete list by itself — and declined by the
   fold. The admission half is what makes the decline a boundary of this slice rather than a
   refusal of the shape. -/
example : starChecked?.isSome = true := by native_decide

example : (starChecked?.map fun checked =>
    match TemporalExtremumStream.eval checked .maximum
        (probeModel.checkContext (raw [])) .validation with
    | .ok _ => none
    | .error error => some error) =
    some (some (.operandNeedsAddressing ["Probe", "Rows", "RowDate"])) := by
  native_decide

end A12Kernel.Conformance.TemporalExtremumStream
