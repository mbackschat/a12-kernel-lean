import A12Kernel.Elaboration.TemporalExtremumStream

/-! # A12Kernel.Conformance.TemporalExtremumStream — the extrema's folds, read from a model

The folds were reachable only from a hand-built stream, so every earlier row about them assumed the
projection these rows now exercise. What is worth locking is each family's own empty rule and its two
failure modes, because each has a plausible wrong account that a single happy-path row would leave
standing: an unspecified operand could contribute a synthetic value the way an empty Number
contributes zero, a malformed one could be skipped like an absent one, and a formally unavailable one
could be skipped rather than aborting.

The three families' rows are not one family's repeated. Date and clock order **decoded labels**;
DateTime orders **exact instants**, and the shape that tells those apart is the repeated hour, where
one wall label names two moments ([`spec/05`](../../spec/05-dates-and-time.md) states it as an exact
selected instant remaining distinct from an equal-looking value across a model-zone overlap).
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
      { id := 7, groupPath := ["Probe"], name := "Clock",
        policy := { kind := .temporal .time TemporalComponents.time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 9, groupPath := ["Probe"], name := "Clock2",
        policy := { kind := .temporal .time TemporalComponents.time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      -- A DATE_TIME at the degenerate time-only format: a different kind, the same component set,
      -- which is the pair the measured gate admits and a kind test would refuse.
      { id := 8, groupPath := ["Probe"], name := "StampAsClock",
        policy := { kind := .temporal .dateTime TemporalComponents.time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 10, groupPath := ["Probe"], name := "Stamp",
        policy := { kind := .temporal .dateTime TemporalComponents.now },
        temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 11, groupPath := ["Probe"], name := "Stamp2",
        policy := { kind := .temporal .dateTime TemporalComponents.now },
        temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      { id := 6, groupPath := ["Probe", "Rows"], name := "RowDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" },
        repeatableScope := [20] },
      -- A second repeatable group whose capacity the rows below **fill**. `Rows` above is declared
      -- with spare capacity, so the pair is what makes the uninstantiated-tail marker observable
      -- rather than constant.
      -- Two nonrepeatable Dates in their own group: a fixed-group expansion with no declared row
      -- anywhere under it, so its fold's tail bit is `false` by fact rather than by construction.
      { id := 13, groupPath := ["Probe", "Pair"], name := "PairA",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 14, groupPath := ["Probe", "Pair"], name := "PairB",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      -- A nonrepeatable group holding a repeatable descendant with spare capacity: the shape whose
      -- tail the shared group walk cannot report.
      { id := 15, groupPath := ["Probe", "Box"], name := "BoxDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 16, groupPath := ["Probe", "Box", "Deep"], name := "DeepDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" },
        repeatableScope := [40] },
      { id := 12, groupPath := ["Probe", "Full"], name := "FullRowDate",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" },
        repeatableScope := [30] }]
    repeatableGroups := [
      { level := 20, path := ["Probe", "Rows"], repeatability := some 3 },
      { level := 30, path := ["Probe", "Full"], repeatability := some 2 },
      { level := 40, path := ["Probe", "Box", "Deep"], repeatability := some 3 }] }

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
  (TemporalExtremumStream.evalDate checked op
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

/-! ## The clock family, through the same reader

Adding a family is a projection and a component set, not a second reader, so the rows here are the
ones that could differ: the clock's own selection and empty rule, and each family declining the
other's list — which is what keeps one reader from accepting a value its element type cannot hold. -/

private def timeCell (hour minute second : Nat) : RawCell :=
  match TimeOfDay.ofHms? hour minute second with
  | some parts => .parsed (.temporal (.time { epochMillis := 0 } parts))
  | none => .empty

private def clockFoldOf (names : List String) (op : TemporalExtremumOp)
    (cells : List (FieldId × RawCell)) :
    Option (SimpleComparisonOperand TimeOfDay) := do
  let checked ← admitted? names
  (TemporalExtremumStream.evalTime checked op
    (probeModel.checkContext (raw cells)) .validation).toOption

private def hms (hour minute second : Nat) : Option TimeOfDay :=
  TimeOfDay.ofHms? hour minute second

example : clockFoldOf ["Clock", "Clock2"] .maximum
    [(7, timeCell 9 30 0), (9, timeCell 17 15 45)] =
    ((hms 17 15 45).map fun time => .value time true) := by
  native_decide

example : clockFoldOf ["Clock", "Clock2"] .minimum
    [(7, timeCell 9 30 0), (9, timeCell 17 15 45)] =
    ((hms 9 30 0).map fun time => .value time true) := by
  native_decide

/- The clock family's own empty rule, so it is the Date rule and not a reimplementation: an absent
   operand marks the result incomplete, and an all-empty list yields no value. -/
example : clockFoldOf ["Clock", "Clock2"] .maximum [(7, timeCell 9 30 0)] =
    ((hms 9 30 0).map fun time => .value time false) := by
  native_decide

example : clockFoldOf ["Clock", "Clock2"] .maximum [] = some .notEvaluated := by
  native_decide

/- A Date payload reaching the clock projection is malformed rather than skipped, which is the arm
   that keeps the two families' domains apart at runtime as well as at the gate. -/
example : clockFoldOf ["Clock", "Clock2"] .maximum
    [(7, timeCell 9 30 0), (9, dateCell 2024 3 5)] =
    some (.unknown .malformed) := by
  native_decide

/-! ### The cross-kind clock list folds, which is the pair a kind test would have lost

A TIME beside a **DATE_TIME declared time-only** is the pair the measured component gate admits and a
kind test would refuse, and it reaches the fold because a temporal cell's admitted family is its
declared component set's rather than its declared kind's — the Kernel reads the format at admission,
at the store, and at value comparison alike
([checkpoint](../../docs/SOURCES.md#src-temporal-value-family-is-the-formats-not-the-kinds)). These
rows are the ones that would have gone silently wrong: before that correction the DATE_TIME cell was
malformed, so the fold answered UNKNOWN for a list the Kernel folds. -/

example : (admitted? ["Clock", "StampAsClock"]).isSome = true := by native_decide

example : clockFoldOf ["Clock", "StampAsClock"] .maximum
    [(7, timeCell 9 30 0), (8, timeCell 17 15 45)] =
    ((hms 17 15 45).map fun time => .value time true) := by
  native_decide

/- The cross-kind operand carrying the **selected** value, so the row is not passing because the TIME
   operand happens to win. -/
example : clockFoldOf ["Clock", "StampAsClock"] .minimum
    [(7, timeCell 17 15 45), (8, timeCell 9 30 0)] =
    ((hms 9 30 0).map fun time => .value time true) := by
  native_decide

/- And the DATE_TIME declaration still refuses a **date** payload, so the widening is to its format's
   family and not to anything temporal. -/
example : clockFoldOf ["Clock", "StampAsClock"] .maximum
    [(7, timeCell 9 30 0), (8, dateCell 2024 3 5)] =
    some (.unknown .malformed) := by
  native_decide

/-! ## The DateTime family, whose domain is the instant and not the label

This family's rows are not the clock's rows again with a wider payload. Its element type is the
exact `Instant`, so the one thing worth locking is that the projection hands over the value's
**retained** instant instead of rebuilding one from its wall label — a distinction that is invisible
on every ordinary pair and decides the answer on exactly one shape. -/

private def stampCell (epochMillis : Int) (year month day hour minute second : Nat) : RawCell :=
  match TimeOfDay.ofHms? hour minute second with
  | some clock =>
      .parsed (.temporal
        (.dateTime { epochMillis } { year, month, day } clock .storedGregorian))
  | none => .empty

private def stampFoldOf (names : List String) (op : TemporalExtremumOp)
    (cells : List (FieldId × RawCell)) :
    Option (SimpleComparisonOperand Instant) := do
  let checked ← admitted? names
  (TemporalExtremumStream.evalDateTime checked op
    (probeModel.checkContext (raw cells)) .validation).toOption

example : stampFoldOf ["Stamp", "Stamp2"] .maximum
    [(10, stampCell 1000 2024 3 5 9 30 0), (11, stampCell 5000 2024 3 5 9 30 4)] =
    some (.value { epochMillis := 5000 } true) := by
  native_decide

example : stampFoldOf ["Stamp", "Stamp2"] .minimum
    [(10, stampCell 1000 2024 3 5 9 30 0), (11, stampCell 5000 2024 3 5 9 30 4)] =
    some (.value { epochMillis := 1000 } true) := by
  native_decide

/-- The repeated hour's two payloads, named once so the rows below and the premise they rest on
    describe the same pair. Europe/Berlin passes through the label `2024-10-27T02:15:00` twice on
    that date, at UTC `00:15` and `01:15`, which are these two `epochMillis` an hour apart. -/
private def foldEarlier : RawCell := stampCell 1729988100000 2024 10 27 2 15 0
private def foldLater : RawCell := stampCell 1729991700000 2024 10 27 2 15 0

/- The separator's premise, stated rather than assumed: these two payloads carry the **same** label
   and **different** instants. Without this row the two below could pass under a label account that
   happened to order them correctly; with it, a label account must tie, and a tie keeps its left
   operand, so it cannot answer `Max` and `Min` differently on this pair at all. -/
example :
    (match (probeModel.checkContext (raw [(10, foldEarlier), (11, foldLater)])).observeAt
        .validation 10,
      (probeModel.checkContext (raw [(10, foldEarlier), (11, foldLater)])).observeAt
        .validation 11 with
     | .value (.temporal first), .value (.temporal second) =>
         some ((first.dateParts?, first.time?) == (second.dateParts?, second.time?) &&
           first.instant != second.instant)
     | _, _ => none) = some true := by
  native_decide

/- So a projection that rebuilt the instant from `date` and `time` returns the **same** answer for
   `Max` and `Min` on this pair. Ordering by the retained instant separates them, which is why these
   two rows are the family's whole point and no ordinary pair replaces them. -/
example : stampFoldOf ["Stamp", "Stamp2"] .maximum
    [(10, foldEarlier), (11, foldLater)] =
    some (.value { epochMillis := 1729991700000 } true) := by
  native_decide

example : stampFoldOf ["Stamp", "Stamp2"] .minimum
    [(10, foldEarlier), (11, foldLater)] =
    some (.value { epochMillis := 1729988100000 } true) := by
  native_decide

/- Authored the other way round, so neither row above passes by operand position. -/
example : stampFoldOf ["Stamp", "Stamp2"] .maximum
    [(10, foldLater), (11, foldEarlier)] =
    some (.value { epochMillis := 1729991700000 } true) := by
  native_decide

/- The shared empty rule and malformed arm on this payload, so the family is the siblings' rule and
   not a reimplementation. -/
example : stampFoldOf ["Stamp", "Stamp2"] .maximum
    [(10, stampCell 1000 2024 3 5 9 30 0)] =
    some (.value { epochMillis := 1000 } false) := by
  native_decide

example : stampFoldOf ["Stamp", "Stamp2"] .maximum [] = some .notEvaluated := by
  native_decide

example : stampFoldOf ["Stamp", "Stamp2"] .maximum
    [(10, stampCell 1000 2024 3 5 9 30 0), (11, dateCell 2024 3 5)] =
    some (.unknown .malformed) := by
  native_decide

/- Each reader declines the other's list at the one component-set gate, in both directions: the
   time-only DATE_TIME pair belongs to the clock reader and the complete stamps to this one. Reading
   the family off the declared kind would have sent both lists to this reader. -/
example : (do
    let checked ← admitted? ["Clock", "StampAsClock"]
    match TemporalExtremumStream.evalDateTime checked .maximum
        (probeModel.checkContext (raw [])) .validation with
    | .ok _ => none
    | .error error => some error) =
    some (.componentsMismatch TemporalComponents.now TemporalComponents.time) := by
  native_decide

example : (do
    let checked ← admitted? ["Stamp", "Stamp2"]
    match TemporalExtremumStream.evalTime checked .maximum
        (probeModel.checkContext (raw [])) .validation with
    | .ok _ => none
    | .error error => some error) =
    some (.componentsMismatch TemporalComponents.time TemporalComponents.now) := by
  native_decide

/-! ## The addressed route, where a star finally folds every row

Admission always accepted a starred operand and the flat reader always declined it, so until now no
route folded one. These rows exercise the second entry point, over the immutable checked document.
Three things are worth locking and nothing else is new: that every row reaches the fold in topology
order, that the **uninstantiated tail** weakens the result's given-ness, and that an **over-limit**
row supplies nothing at all. -/

private def prepared :
    PreparedFlatStringContext probeModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler probeModel).toOption.get (by native_decide)

/-- One row of one repeatable group holding one stored Date. -/
private def rowCell (field : FieldId) (row : Nat) (year month day : Nat) :
    ClassifiedCellInput := {
  address := { field, path := [row] }
  stored := "stored"
  raw := dateCell year month day }

private def document? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument probeModel) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def rowStarOperand (group field : String) : SurfaceFieldEntityOperand :=
  .star { base := .absolute
          groups := [{ name := "Probe" }, { name := group, starred := true }]
          field }

private def addressedFoldOf (operands : List SurfaceFieldEntityOperand)
    (op : TemporalExtremumOp) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (SimpleComparisonOperand FullDate) := do
  let checked ←
    (TemporalExtremumOperands.elaborate probeModel ["Probe"]
      (match operands with
       | [] => sourceOf []
       | first :: rest => { first, rest })).toOption
  let document ← document? rows cells
  (TemporalExtremumStream.evalAddressedDate checked op document []
    .validation).toOption

/- Two instantiated rows, folded. `Rows` is declared with capacity **3**, so this list carries an
   uninstantiated tail and the selected value is not given — which is the marker the flat route had
   no way to set. -/
example : addressedFoldOf [rowStarOperand "Rows" "RowDate"] .maximum
    [{ group := 20, path := [1] }, { group := 20, path := [2] }] [rowCell 6 1 2024 3 5, rowCell 6 2 2024 7 1] =
    ((ymd 2024 7 1).map fun date => .value date false) := by
  native_decide

/- The same two rows in a group whose capacity they **fill**: the tail closes and the identical
   selection becomes given. Without this pair the flag above would be indistinguishable from a
   constant `false` on every starred operand. -/
example : addressedFoldOf [rowStarOperand "Full" "FullRowDate"] .maximum
    [{ group := 30, path := [1] }, { group := 30, path := [2] }] [rowCell 12 1 2024 3 5, rowCell 12 2 2024 7 1] =
    ((ymd 2024 7 1).map fun date => .value date true) := by
  native_decide

example : addressedFoldOf [rowStarOperand "Full" "FullRowDate"] .minimum
    [{ group := 30, path := [1] }, { group := 30, path := [2] }] [rowCell 12 1 2024 3 5, rowCell 12 2 2024 7 1] =
    ((ymd 2024 3 5).map fun date => .value date true) := by
  native_decide

/- A scalar operand beside the star: both reach one fold, and the scalar's later date wins over every
   row, so the two forms compose in one list rather than one shadowing the other. -/
example : addressedFoldOf
    [fieldOperand "A", rowStarOperand "Full" "FullRowDate"] .maximum
    [{ group := 30, path := [1] }, { group := 30, path := [2] }]
    [{ address := { field := 1, path := [] }, stored := "stored",
       raw := dateCell 2025 1 1 },
     rowCell 12 1 2024 3 5, rowCell 12 2 2024 7 1] =
    ((ymd 2025 1 1).map fun date => .value date true) := by
  native_decide

/-! ### The over-limit row supplies nothing, and the two accounts genuinely differ here

The declared-capacity extent is a property of the operand rather than of the consuming operator
([checkpoint](../../docs/SOURCES.md#src-capacity-consumer-sweep)). The extremum is the first consumer
for which that choice is not a formality: an over-limit cell is formally unavailable, and this fold
**aborts** on an unavailable operand where the sweep's uniqueness carrier merely skips one. So the
complete view would answer UNKNOWN for a document the Kernel folds, and the two rows below say which
account ships and prove the other is not the same answer by luck. -/

private def overLimitRows : List RowAddr :=
  [{ group := 30, path := [1] }, { group := 30, path := [2] },
   { group := 30, path := [3] }]

private def overLimitCells : List ClassifiedCellInput :=
  [rowCell 12 1 2024 3 5, rowCell 12 2 2024 4 1, rowCell 12 3 2024 12 31]

/- Capacity 2, three rows, and the **latest** date sits in the third. The answer is April, given, so
   row three neither won nor terminalized: it supplied nothing. -/
example : addressedFoldOf [rowStarOperand "Full" "FullRowDate"] .maximum
    overLimitRows overLimitCells =
    ((ymd 2024 4 1).map fun date => .value date true) := by
  native_decide

/- The premise, stated rather than assumed: that third cell is formally unavailable and projects to
   an UNKNOWN operand, which is exactly what the fold aborts on. So the row above is the extent
   account and not an agreement between two readings. -/
example : (do
    let document ← document? overLimitRows overLimitCells
    let addressed ← (document.addressedCell [(30, 3)] 12).toOption
    some (addressed.cell.findings,
      CellObservation.asDateExtremumOperand
        (observeCell .validation addressed.cell))) =
    some ([.overRepetition], .unknown .overRepetition) := by
  native_decide

/- The **filtered** star never reaches either reader, because admission refuses it: no route here
   elaborates a `Having`, and folding an unfiltered row set for a filtered operand would answer a
   different question. The addressed reader keeps a totality arm for the form anyway, so a future
   admission widening surfaces as a decline rather than as a silent unfiltered fold — this row is
   what makes that arm's premise checked rather than asserted. -/
private def selfFilter : SurfaceCorrelatedHaving :=
  .presence .filled
    { origin := .inner
      field := { base := .absolute, groups := ["Probe", "Full"],
                 field := "FullRowDate" } }

example : (TemporalExtremumOperands.elaborate probeModel ["Probe"]
    { first := .starHaving
        { base := .absolute
          groups := [{ name := "Probe" }, { name := "Full", starred := true }]
          field := "FullRowDate" } selfFilter
      rest := [] }).toOption.isNone = true := by
  native_decide

/-! ### A fixed group, and the tail bit that decides which ones it may fold

A group operand asks the shared owner **two** questions, and neither implies the other. The walk
gives its concrete `(row x field)` extent and enumerates only **instantiated** rows, so its own tail
bit is `false` by construction; the tail query gives whether any reopened declaration retains
declared-but-uninstantiated capacity. `spec/05` ties this fold's `given` flag to the second, so asking
only the first folded a subtree with spare capacity to a **given** value where the Kernel's is not
given — a wrong flag on a right value, which no case would have caught. The three rows below vary
exactly the document against one declaration. -/

private def fixedGroupOperand (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def groupFoldValue? (groups : GroupPath) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (SimpleComparisonOperand FullDate) := do
  let checked ←
    (TemporalExtremumOperands.elaborate probeModel ["Probe"]
      { first := fixedGroupOperand groups, rest := [] }).toOption
  let document ← document? rows cells
  (TemporalExtremumStream.evalAddressedDate checked .maximum document []
    .validation).toOption

/- Two scalar Dates in their own group: folded, and **given** — no declared row exists anywhere under
   the expansion, so the walk's `false` tail is the fact rather than an artefact. -/
example : groupFoldValue? ["Probe", "Pair"] []
    [{ address := { field := 13, path := [] }, stored := "s",
       raw := dateCell 2024 3 5 },
     { address := { field := 14, path := [] }, stored := "s",
       raw := dateCell 2024 7 1 }] =
    ((ymd 2024 7 1).map fun date => .value date true) := by
  native_decide

/- The same shape one repeatable descendant deeper — declared capacity 3, one row instantiated, and
   the later date inside it. It folds, and the result is **not given**: the two uninstantiated rows
   are the provenance, and they come from the tail query rather than from the walk. Asking only the
   walk answered `given` here, which is the divergence this row guards. -/
example : groupFoldValue? ["Probe", "Box"] [{ group := 40, path := [1] }]
    [{ address := { field := 15, path := [] }, stored := "s",
       raw := dateCell 2024 1 1 },
     { address := { field := 16, path := [1] }, stored := "s",
       raw := dateCell 2024 7 1 }] =
    ((ymd 2024 7 1).map fun date => .value date false) := by
  native_decide

/- Filling the declared capacity closes the tail on the identical selection, so the flag tracks the
   declaration against the document rather than the mere presence of a repeatable descendant. -/
example : groupFoldValue? ["Probe", "Box"]
    [{ group := 40, path := [1] }, { group := 40, path := [2] },
     { group := 40, path := [3] }]
    [{ address := { field := 15, path := [] }, stored := "s",
       raw := dateCell 2024 1 1 },
     { address := { field := 16, path := [1] }, stored := "s",
       raw := dateCell 2024 7 1 },
     { address := { field := 16, path := [2] }, stored := "s",
       raw := dateCell 2024 2 1 },
     { address := { field := 16, path := [3] }, stored := "s",
       raw := dateCell 2024 3 1 }] =
    ((ymd 2024 7 1).map fun date => .value date true) := by
  native_decide

/-! ## What this slice declines, and why each is a boundary rather than a verdict -/

private def refusal? (names : List String) :
    Option TemporalExtremumStreamError := do
  let checked ← admitted? names
  match TemporalExtremumStream.evalDate checked .maximum
      (probeModel.checkContext (raw [])) .validation with
  | .ok _ => none
  | .error error => some error

/- A component-omitting list is **admitted as an operand list** and declined by the fold, which is
   the split this capsule rests on: admission is measured, the ordering of such values is not. -/
example : (admitted? ["Month", "Month2"]).isSome = true := by native_decide

example : refusal? ["Month", "Month2"] =
    some (.componentsMismatch TemporalComponents.fullDate yearMonth) := by
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
    match TemporalExtremumStream.evalDate checked .maximum
        (probeModel.checkContext (raw [])) .validation with
    | .ok _ => none
    | .error error => some error) =
    some (some (.operandNeedsAddressing ["Probe", "Rows", "RowDate"])) := by
  native_decide

end A12Kernel.Conformance.TemporalExtremumStream
