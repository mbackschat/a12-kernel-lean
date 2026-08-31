import A12Kernel.Elaboration.NumericComputation

/-! # Static admission of a starred group-count operand in the computation arm

`NumberOfFilledGroups` admits a starred repeatable operand, alone or beside a fixed one, and the
arity gate is conditional on the star: one operand is legal exactly when it is starred, while the
two-operand minimum governs the unstarred form. All four rows are measured on both Kernel codegen
strategies at the [starred group-count
checkpoint](../../../docs/SOURCES.md#src-starred-group-count-computation) through
`computation add --dry-run`, each `verification: KERNEL_CONFIRMED`.

The runtime half is locked here too, against the same checkpoint's counted rows. The starred operand's contribution is a row count, whose
fold is owned by `numberOfFilledGroupsForComputationOperands` and locked at the clause in
`Conformance/StarredGroupCountComputation.lean`; what these cases add is that a checked operand list
reaches it over a real document. The scalar route has no row topology and refuses, which is correct
rather than incomplete.
-/

namespace A12Kernel.Conformance.NumericComputation.StarredGroupCount

open A12Kernel

private def flatValueId : FieldId := 0
private def rowValueId : FieldId := 1
private def targetId : FieldId := 2
private def otherValueId : FieldId := 3
private def otherRowValueId : FieldId := 4

private def numberPolicy : FieldPolicy := { kind := .number { scale := 0, signed := true } }

private def numberIn (id : FieldId) (groupPath : GroupPath) (name : String) : FlatFieldDecl where
  id
  groupPath
  name
  policy := numberPolicy

private def rowsLevel : RepeatableLevel := 10
private def othersLevel : RepeatableLevel := 11

/-- One fixed group beside a repeatable one, both under the declaring root, mirroring the shape of
    the model the checkpoint above measured. -/
private def model : FlatModel :=
  { fields :=
      [ numberIn flatValueId ["Probe", "Flat"] "FlatValue"
      , numberIn otherValueId ["Probe", "Other"] "OtherValue"
      , { numberIn rowValueId ["Probe", "Rows"] "RowValue" with
            repeatableScope := [rowsLevel] }
      , { numberIn otherRowValueId ["Probe", "Others"] "OtherRowValue" with
            repeatableScope := [othersLevel] }
      , numberIn targetId ["Probe"] "Target" ]
    repeatableGroups :=
      [ { level := rowsLevel, path := ["Probe", "Rows"], repeatability := some 5 }
      , { level := othersLevel, path := ["Probe", "Others"], repeatability := some 4 } ] }

private def fixedOperand (path : GroupPath) : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := path })

/-- A second repeatable group, so a list can carry two independent cardinalities. -/
private def starredOthers : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Others"] }

/-- `Rows*` — the wildcard sits on the terminal group. -/
private def starredOperand : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "Rows"] }

/-- `Rows` without its star, which the Kernel refuses. -/
private def unstarredRepeatable : SurfaceGroupCountOperand :=
  fixedOperand ["Probe", "Rows"]

private def admissionOf (operands : List SurfaceGroupCountOperand) :
    Except NumericComputationElabError Unit :=
  (elaborateNumericComputationOperation model ["Probe"] targetId
    (.atom (.filledGroupCount operands))).map fun _ => ()

private def admitted (operands : List SurfaceGroupCountOperand) : Bool :=
  (admissionOf operands).toOption.isSome

/- A single starred operand is a complete list. This is the row that shows the arity gate is not
   an operand count: the same group unstarred is refused below, and a lone fixed operand is too. -/
example : admitted [starredOperand] = true := by
  native_decide

/- The mixed list, admitted. Its two operands contribute unlike quantities at runtime. -/
example : admitted [fixedOperand ["Probe", "Flat"], starredOperand] = true := by
  native_decide

/- A repeatable operand written without its star is refused. Measured `MVK_NO_WILDCARD`. -/
example : admitted [unstarredRepeatable] = false := by
  native_decide

/- A lone fixed operand is refused for a different reason — measured `MVK_PARAMSIZE_INVALIDGN`,
   *"There must be more than one group"* — which is what makes the first row a statement about
   the star rather than about arity. -/
example : admitted [fixedOperand ["Probe", "Flat"]] = false := by
  native_decide

/- The established fixed pair still elaborates, so admitting the starred form widened the operand
   list without disturbing the form that was already there. -/
example : admitted [fixedOperand ["Probe", "Flat"], fixedOperand ["Probe", "Other"]] = true := by
  native_decide

/-! ### Containment and rootness over a mixed list

The whole static gate table is **arm-independent**: every class the validation arm draws over a
mixed operand list, the computation arm draws identically, in both authored orders, measured through
`computation add --dry-run` on a two-root model
([checkpoint](../../../docs/SOURCES.md#src-group-count-static-gates-both-arms)). The arm boundary is
real for polarity — a computation's count carries none — so reusing the validation arm's gates here
is a claim, and this is the measurement that discharges it.
-/

private def gateNested : FieldId := 5
private def gateInner : FieldId := 6
private def gateSecond : FieldId := 7
private def gateTarget : FieldId := 8

private def nestedLevel : RepeatableLevel := 12
private def innerLevel : RepeatableLevel := 13
private def secondLevel : RepeatableLevel := 14

/-- A repeatable group under a **fixed** one, a repeatable group under a **repeatable** one, and a
    repeatable group under a **second root**. Those three carriers are what the model above lacks:
    every containment pair and the disjoint-root control need one of them. -/
private def gateModel : FlatModel :=
  { fields :=
      [ numberIn flatValueId ["Probe", "Flat"] "FlatValue"
      , { numberIn gateNested ["Probe", "Flat", "Nested"] "NestedValue" with
            repeatableScope := [nestedLevel] }
      , { numberIn rowValueId ["Probe", "Rows"] "RowValue" with
            repeatableScope := [rowsLevel] }
      , { numberIn gateInner ["Probe", "Rows", "Inner"] "InnerValue" with
            repeatableScope := [rowsLevel, innerLevel] }
      , { numberIn gateSecond ["Second", "SRows"] "SecondRowValue" with
            repeatableScope := [secondLevel] }
      , numberIn gateTarget ["Probe"] "GateTarget" ]
    repeatableGroups :=
      [ { level := rowsLevel, path := ["Probe", "Rows"], repeatability := some 3 }
      , { level := nestedLevel, path := ["Probe", "Flat", "Nested"], repeatability := some 2 }
      , { level := innerLevel, path := ["Probe", "Rows", "Inner"], repeatability := some 2 }
      , { level := secondLevel, path := ["Second", "SRows"], repeatability := some 3 } ] }

private def gateCode? (operands : List SurfaceGroupCountOperand) : Option KernelStaticDiagnostic :=
  match elaborateNumericComputationOperation gateModel ["Probe"] gateTarget
      (.atom (.filledGroupCount operands)) with
  | .error error => NumericComputationElabError.groupCountDiagnostic? error
  | .ok _ => none

private def gateStar (path : GroupPath) : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := path }

/- Strict containment refuses whichever side carries the star and in whichever order. The disjoint
   mixed pair beside it is admitted, so the refusals are the containment and not the mixing. -/
example :
    (gateCode? [fixedOperand ["Probe", "Flat"], gateStar ["Probe", "Flat", "Nested"]],
      gateCode? [gateStar ["Probe", "Flat", "Nested"], fixedOperand ["Probe", "Flat"]],
      gateCode? [gateStar ["Probe", "Rows"], gateStar ["Probe", "Rows", "Inner"]],
      gateCode? [fixedOperand ["Probe", "Flat"], gateStar ["Probe", "Rows"]]) =
    (some .duplicateParam2, some .duplicateParam2, some .duplicateParam2, none) := by
  native_decide

/- Two stars naming the **same** group are admitted and count once per position, which is the
   exception that makes the rule containment rather than distinctness. -/
example : gateCode? [gateStar ["Probe", "Rows"], gateStar ["Probe", "Rows"]] = none := by
  native_decide

/- A root operand beside a disjoint star draws the root class in either order, and containment wins
   over it when the star lies inside the root. The live control is a nonroot fixed group beside
   another root's star. -/
example :
    (gateCode? [fixedOperand ["Probe"], gateStar ["Second", "SRows"]],
      gateCode? [gateStar ["Second", "SRows"], fixedOperand ["Probe"]],
      gateCode? [fixedOperand ["Probe"], gateStar ["Probe", "Rows"]],
      gateCode? [fixedOperand ["Probe", "Flat"], gateStar ["Second", "SRows"]]) =
    (some .rootGroupWithOtherParameters, some .rootGroupWithOtherParameters,
      some .duplicateParam2, none) := by
  native_decide

/-! ## Runtime -/

private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }

private def filledNumber : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

/-- Instantiated rows of each repeatable group, none of them carrying a cell. -/
private def documentWith (rows others : Nat) : Document :=
  { instantiatedRows :=
      (List.range rows).map (fun index => { group := rowsLevel, path := [index + 1] }) ++
        (List.range others).map fun index => { group := othersLevel, path := [index + 1] }
    rawCells := fun _ => none }

private def evaluationContext (flatFilled : Bool) (rows others : Nat) :
    NumericComputationEvaluationContext :=
  { scalar := { read := fun id => if id == flatValueId && flatFilled then filledNumber else emptyCell }
    document := documentWith rows others
    outer := []
    filterRead := fun _ _ => emptyCell
    starRead := fun _ _ => emptyCell }

private def countOf (operands : List SurfaceGroupCountOperand)
    (flatFilled : Bool) (rows : Nat) (others : Nat := 0) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Probe"] targetId
      (.atom (.filledGroupCount operands)) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom atom =>
          ((evaluationContext flatFilled rows others).readCheckedNumericComputationAtom atom).toOption
      | _ => none


private def mixedList : List SurfaceGroupCountOperand :=
  [fixedOperand ["Probe", "Flat"], starredOperand]

private def scalarCountOf (operands : List SurfaceGroupCountOperand) :
    Option NumericComputationFault :=
  match elaborateNumericComputationOperation model ["Probe"] targetId
      (.atom (.filledGroupCount operands)) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom atom =>
          match ScalarComputationContext.readCheckedNumericComputationAtom
              { read := fun _ => emptyCell } atom with
          | .error fault => some fault
          | .ok _ => none
      | _ => none

/- The starred operand alone contributes the instantiated row count. No row here carries a cell at
   all, so three rows counting three is the discriminator: a presence account answers one. -/
example :
    [countOf [starredOperand] true 0, countOf [starredOperand] true 1,
      countOf [starredOperand] true 2, countOf [starredOperand] true 3] =
      [some (.value 0), some (.value 1), some (.value 2), some (.value 3)] := by
  native_decide

/- The mixed list, in the arithmetic a12-dmkits measured independently on its own model: the fixed
   operand's zero-or-one plus the starred operand's cardinality, into one sum. Row two is the
   separator — emptying the fixed group drops the total by exactly one while every row still
   counts, so the two contributions are independent and unlike. -/
example :
    [countOf mixedList true 3, countOf mixedList false 3,
      countOf mixedList true 0, countOf mixedList false 0] =
      [some (.value 4), some (.value 3), some (.value 1), some (.value 0)] := by
  native_decide

/- The scalar route refuses the same checked atom rather than answering a fixed-only count for it.
   Its whole input is a cell read, so this is a correct refusal and not a missing case. -/
example : scalarCountOf mixedList = some .repeatableContextRequired := by
  native_decide

/-! ## Two starred operands

The **runtime** numbers below are measured — on a12-dmkits' kernel oracle, at the [two-star
rows](../../../docs/SOURCES.md#src-starred-group-count-computation) — and the fold that produces
them is replayed against those rows at its owning clause in
`Conformance/StarredGroupCountComputation.lean`. What these cases add is that an elaborated
operand list reaches that fold.

Static admission is measured on the same estate, through the Kernel's own model check, so each
case below asserting it silently by answering at all is now backed rather than inherited from
[§1](../../../spec/02-logic-and-formal-errors.md)'s wildcard-duplicate gate. Both halves rest on
one estate: this project's own rows for these shapes were observed in a window that could not be
certified clean and are not cited.
-/

/- Two independent cardinalities add, and neither operand's rows reach the other's count. -/
example :
    [countOf [starredOperand, starredOthers] false 3 2,
      countOf [starredOperand, starredOthers] false 3 0,
      countOf [starredOperand, starredOthers] false 0 0] =
      [some (.value 5), some (.value 3), some (.value 0)] := by
  native_decide

/- An indicator and two cardinalities in one list, which is the widest admitted shape here. -/
example : countOf [fixedOperand ["Probe", "Flat"], starredOperand, starredOthers] true 3 2 =
    some (.value 6) := by
  native_decide

/- The **duplicate**, admitted rather than refused: a repeated starred group is a repeated authored
   occurrence, so its cardinality is added once per occurrence. Nothing deduplicates it, which is
   why the fixed operands' overlap gate is deliberately not extended over starred ones. -/
example :
    countOf [starredOperand, starredOperand] false 3 0 = some (.value 6) ∧
      countOf [starredOperand] false 3 0 = some (.value 3) := by
  native_decide

/-! ## An operand whose group contains another operand's

A fixed operand naming an **ancestor** of a starred operand's group is the shape where the two
could interfere, because the ancestor's only content is the very rows the star counts. This project
answered it — the pair counts twice, with no overlap gate and no deduplication — and that answer is
**falsified**: the Kernel never reaches the runtime, refusing the pair `MVK_DUPLICATE_PARAM2` at
authoring time, in either order, on a pure shell exactly as on a group with a field of its own
([checkpoint](../../../docs/SOURCES.md#src-group-count-static-gates-both-arms)). The counting cases
that stood here locked an unauthorable shape; the gate table above replaces them.
-/

/-! ## A starred group that owns its own repeatable descendant

The starred operand's own extent, on a group whose rows each contain a second repetition level.
Measured at the [row-domain checkpoint](../../../docs/SOURCES.md#src-group-count-row-domains) on
both codegen strategies.
-/

private def midLevel : RepeatableLevel := 13
private def deepRowsLevel : RepeatableLevel := 14

/-- `Mid` repeats and each of its rows owns the repeatable `Rows` below it. -/
private def twoLevelModel : FlatModel :=
  { fields :=
      [ numberIn flatValueId ["Probe", "Flat"] "FlatValue"
      , { numberIn rowValueId ["Probe", "ShellDeep", "Mid", "Rows"] "DeepValue" with
            repeatableScope := [midLevel, deepRowsLevel] }
      , numberIn targetId ["Probe"] "Target" ]
    repeatableGroups :=
      [ { level := midLevel, path := ["Probe", "ShellDeep", "Mid"], repeatability := some 3 }
      , { level := deepRowsLevel, path := ["Probe", "ShellDeep", "Mid", "Rows"],
          repeatability := some 5 } ] }

private def midStar : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := ["Probe", "ShellDeep", "Mid"] }

private def twoLevelCount (rows : List RowAddr) : Option NumericComputationResult :=
  match elaborateNumericComputationOperation twoLevelModel ["Probe"] targetId
      (.atom (.filledGroupCount [midStar])) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom atom =>
          ((⟨{ read := fun _ => emptyCell },
             { instantiatedRows := rows, rawCells := fun _ => none },
             [], fun _ _ => emptyCell, fun _ _ => emptyCell⟩ :
            NumericComputationEvaluationContext).readCheckedNumericComputationAtom
              (model := twoLevelModel) atom).toOption
      | _ => none

private def midRow (index : Nat) : RowAddr := { group := midLevel, path := [index] }
private def deepRow (outer inner : Nat) : RowAddr :=
  { group := deepRowsLevel, path := [outer, inner] }

/- The operand counts **its own** rows and the repeatable level below it does not disturb them: two
   `Mid` rows each carrying a leaf row count two, not four and not one. An account folding the inner
   level into the same quantity answers four here. -/
example :
    [twoLevelCount [], twoLevelCount [midRow 1],
      twoLevelCount [midRow 1, deepRow 1 1, midRow 2, deepRow 2 1]] =
      [some (.value 0), some (.value 1), some (.value 2)] := by
  native_decide

/- **The over-limit row, on this carrier rather than inherited from the flat one.** Four rows in a
   `max 3` group count three, so the starred operand's in-capacity domain survives the descendant
   that makes this group different from the one where that rule was first measured. -/
example : twoLevelCount [midRow 1, midRow 2, midRow 3, midRow 4] = some (.value 3) := by
  native_decide

/-! ## Growth channels, and the message type they feed

The same checked operand list read for the *other* question the Kernel asks of it. These close the
route from an authored computation to its implicit self-validation message type, which the
[message-polarity checkpoint](../../../docs/SOURCES.md#src-starred-operand-message-polarity)
measures over a model of this shape with `Rows` declared `max 5`.
-/

/-- The same model with the repeatable group's declared maximum withheld, which the staged model
    boundary permits. Its starred operand still evaluates; only its *movement* is unknown. -/
private def unboundedModel : FlatModel :=
  { model with
      repeatableGroups := model.repeatableGroups.map fun group =>
        if group.level == rowsLevel then { group with repeatability := none } else group }

private def growthIn (target : FlatModel) (operands : List SurfaceGroupCountOperand)
    (flatFilled : Bool) (rows : Nat) (others : Nat := 0) :
    Option (Option (List ComputationOperandGrowth)) :=
  match elaborateNumericComputationOperation target ["Probe"] targetId
      (.atom (.filledGroupCount operands)) with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom (.filledGroupCountMixed checkedOperands) =>
          ((evaluationContext flatFilled rows others).growthOfGroupCountOperands
            target checkedOperands).toOption
      | _ => none

/- **The fail-closed suppression, which is the branch that must not read as "closed".** A starred
   group whose model retains no finite extent has unknown movement, so the whole list yields no
   channels rather than a closed one — a missing channel read as closed would silently type the
   message VALUE. The bound model beside it is the control: same operands, same document, channels
   present. -/
example :
    growthIn unboundedModel mixedList true 3 = some none ∧
      growthIn model mixedList true 3 = some (some [.fixedGroup true, .starredGroupCount 3 5]) := by
  native_decide

/- The suppression is confined to growth: the same operand list still **counts** on the unbounded
   model, so withholding the declared maximum removes a movement rule and not an evaluation. -/
example :
    (match elaborateNumericComputationOperation unboundedModel ["Probe"] targetId
        (.atom (.filledGroupCount mixedList)) with
      | .error _ => none
      | .ok checked =>
          match checked.core.expression with
          | .atom atom =>
              ((evaluationContext true 3 0).readCheckedNumericComputationAtom
                (model := unboundedModel) atom).toOption
          | _ => none) = some (.value 4) := by
  native_decide

private def growthOf (operands : List SurfaceGroupCountOperand)
    (flatFilled : Bool) (rows : Nat) (others : Nat := 0) :
    Option (Option (List ComputationOperandGrowth)) :=
  growthIn model operands flatFilled rows others

/-- The measured type of a target seeded past any reachable count. -/
private def typeOf (computed : Rat) (channels : Option (Option (List ComputationOperandGrowth))) :
    Option Verdict :=
  match channels with
  | some (some channels) => some (computedNumberSelfValidation 99 computed channels)
  | _ => none

/- Elaboration yields the declared capacity beside the instantiated count, so the channel is read
   against the model rather than against the document alone. -/
example :
    growthOf mixedList true 4 = some (some [.fixedGroup true, .starredGroupCount 4 5]) ∧
      growthOf mixedList true 5 = some (some [.fixedGroup true, .starredGroupCount 5 5]) := by
  native_decide

/- **The capacity boundary, end to end from an authored operand list.** One row of remaining
   capacity is the whole difference between the two message types, and nothing outside the operand
   list changes between them. -/
example :
    typeOf 5 (growthOf mixedList true 4) = some (.fired .omission) ∧
      typeOf 6 (growthOf mixedList true 5) = some (.fired .value) := by
  native_decide

/- Emptying the fixed operand reopens a channel the exhausted starred one no longer has, so the
   at-capacity target types OMISSION again — the fixed channel acting alone. No measured document
   holds that combination; this is the clause's own consequence and carries no external claim. -/
example : typeOf 5 (growthOf mixedList false 5) = some (.fired .omission) := by
  native_decide

/- **The inventory is an authored shape, not a reached-cell trace.** A starred operand names its
   row field with no document in hand at all — the function takes none — which is why the measured
   no-row documents still list `Rows`' field. Both operand forms use the one subtree extent, so the
   fixed and starred halves are indistinguishable in the field set; the difference the Kernel does
   render lives in the coordinates, which this project does not model. -/
example :
    (match elaborateNumericComputationOperation model ["Probe"] targetId
        (.atom (.filledGroupCount mixedList)) with
      | .error _ => none
      | .ok checked =>
          match checked.core.expression with
          | .atom (.filledGroupCountMixed operands) =>
              some (referencedFieldsForFilledGroupCount model operands targetId)
          | _ => none) =
      some [flatValueId, rowValueId, targetId] := by
  native_decide

/- **An over-limit row adds no headroom, and the producer is where that is decided.** Six and seven
   instantiated rows in a `max 5` group yield the same channel as five, because the producer counts
   in-capacity rows before building it. The measured documents type VALUE on all four targets at
   five, six and seven rows alike ([checkpoint](../../../docs/SOURCES.md#src-starred-group-count-computation)),
   which this reproduces — but they do not separate a physical-row reading from an in-capacity one
   at the *type*, since both are closed once the count reaches capacity. What separates them is the
   channel itself, so that is what this asserts. -/
example :
    growthOf mixedList true 6 = some (some [.fixedGroup true, .starredGroupCount 5 5]) ∧
      growthOf mixedList true 7 = some (some [.fixedGroup true, .starredGroupCount 5 5]) := by
  native_decide

/- The type those channels produce, at the measured seed no count can reach. -/
example :
    typeOf 6 (growthOf mixedList true 6) = some (.fired .value) ∧
      typeOf 6 (growthOf mixedList true 7) = some (.fired .value) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.StarredGroupCount
