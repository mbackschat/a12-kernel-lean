import A12Kernel.Elaboration.AddressedRepetitionComputation

namespace A12Kernel.Conformance.AddressedRepetitionComputation

private def outerPath : GroupPath := ["Root", "Rows"]
private def innerPath : GroupPath := outerPath ++ ["Items"]
private def fixedPath : GroupPath := innerPath ++ ["Fixed"]
private def asidePath : GroupPath := ["Root", "Aside"]
/-- `yyyy-MM-dd`: the date half only, so a time component is the temporal row's own separator. -/
private def dateComponents : TemporalComponents :=
  { year := true, month := true, day := true, hour := false, minute := false, second := false }
private def target : FlatFieldDecl :=
  { id := 1, groupPath := innerPath, name := "Target", repeatableScope := [10, 20]
    policy := { kind := .number { scale := 0, signed := true } }
    numericTargetConstraints := { maximum := some 22 } }
private def textDecl : FlatFieldDecl :=
  { target with id := 6, name := "Text", policy := { kind := .string }, numericTargetConstraints := {} }
private def whenDecl : FlatFieldDecl :=
  { target with id := 8, name := "When", policy := { kind := .temporal .date dateComponents }, numericTargetConstraints := {} }
private def model : FlatModel :=
  { fields := [target, { target with id := 2, name := "Base" },
      { target with id := 3, groupPath := fixedPath, name := "FixedField" },
      { target with id := 4, groupPath := ["Root"], name := "Scalar", repeatableScope := [] },
      { target with id := 5, groupPath := outerPath, name := "OuterTarget", repeatableScope := [10] },
      -- Non-Number sources for the widened operand set: one bound by the target's own scope and one
      -- bound by a disjoint repeatable level, which is the separator the scope rule must refuse.
      textDecl,
      { target with id := 7, groupPath := asidePath, name := "AsideText", repeatableScope := [30], policy := { kind := .string }, numericTargetConstraints := {} },
      whenDecl]
    repeatableGroups := [
      { level := 10, path := outerPath, repeatability := some 3 },
      { level := 20, path := innerPath, repeatability := some 3 },
      { level := 30, path := asidePath, repeatability := some 3 }]
    baseYear := some 2020 }
private def repetition (path : GroupPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := path })
private def field (name : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .relative 0, groups := [], field := name })
private def literal (value : Rat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }
private def scalar : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .absolute, groups := ["Root"], field := "Scalar" })
private def mixed : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (.binary .multiply (repetition outerPath) (literal 10))
    (repetition innerPath)
private def operation (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
  checkAddressedRepetitionComputation model innerPath 1 expression
private def read (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  .ok (target.checkRaw (.parsed (.num (if address.path == [2, 3] then 7 else 9))))
private def evaluate? (expression : AuthoredNumericExpr SurfaceNumericAtom) (environment : Env) :
    Option (Sum EnvBindingError NumericComputationResult) := do
  let checked ← (operation expression).toOption
  match checked.evaluateAtEnvironmentWithRead read environment with
  | .ok value => some (.inr value)
  | .error (.environment error) => some (.inl error)
  | .error _ => none

example : evaluate? (repetition fixedPath) [(10, 2), (20, 3)] = some (.inr (.value 1)) ∧
    evaluate? (repetition ["Root"]) [(10, 2), (20, 3)] = some (.inr (.value 1)) ∧
    evaluate? mixed [(10, 2), (20, 3)] = some (.inr (.value 23)) ∧
    evaluate? (.binary .add (repetition innerPath) (field "Base")) [(10, 2), (20, 3)] =
      some (.inr (.value 10)) ∧
    evaluate? (.binary .add (repetition innerPath) scalar) [(10, 2), (20, 3)] =
      some (.inr (.value 12)) := by native_decide

example : evaluate? (repetition fixedPath) [(20, 3)] =
      some (.inl (.missingBinding 10)) ∧
    evaluate? (repetition innerPath) [(10, 0), (20, 3)] =
      some (.inl (.zeroBinding 10)) := by native_decide

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)
private def input : CheckedDocument model :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [2, 3] }, { group := 20, path := [2, 1] },
      { group := 20, path := [2, 2] }, { group := 20, path := [2, 4] }]
    cells := [] }).toOption.get (by native_decide)
private def outcomes? (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (List (List Nat × NumericTargetOutcome)) := do
  let checked ← (operation expression).toOption
  let outcomes ← (checked.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField.path, entry.outcome))

example : outcomes? mixed = some [
    ([2, 3], .rejected { unscaled := 23, scale := 0 } .aboveMaximum),
    ([2, 1], .accepted { unscaled := 21, scale := 0 }),
    ([2, 2], .accepted { unscaled := 22, scale := 0 }), ([2, 4], .noValue)] ∧
    outcomes? (repetition fixedPath) = some [
    ([2, 3], .accepted { unscaled := 1, scale := 0 }),
    ([2, 1], .accepted { unscaled := 1, scale := 0 }),
    ([2, 2], .accepted { unscaled := 1, scale := 0 }), ([2, 4], .noValue)] := by
  native_decide

example : ((operation mixed).toOption.map fun checked =>
    (checked.target.targetDeclaration.repeatableScope, checked.referencesField 1,
      checked.referencesField 2)) = some ([10, 20], false, false) ∧
    ((operation (.binary .add (repetition innerPath) (field "Base"))).toOption.map
      (·.referencesField 2)) = some true := by native_decide

example : (checkAddressedRepetitionComputation model ["Root"] 1 mixed).isOk = true ∧
    (match checkAddressedRepetitionComputation model ["Root"] 5 (repetition innerPath) with
      | .error error => some error
      | .ok _ => none) = some (.repetition (.repeatableGroupRequiresAddress innerPath)) ∧
    (operation (.binary .add (repetition innerPath) (field "Target"))).isOk = false ∧
    (operation (.binary .add (literal 1) (field "Base"))).isOk = false := by native_decide

example :
    let checked := (operation mixed).toOption.get (by native_decide)
    let source : BoundCurrentRepetitionSource := { path := innerPath, scope := [10, 20], level := some 20 }
    checked.target.admitsRepetitionOperand (.boundCurrentRepetition source) = true ∧
      checked.target.admitsRepetitionOperand (.boundCurrentRepetition { source with scope := [20] }) = false ∧
      checked.target.admitsRepetitionOperand (.boundCurrentRepetition { source with level := none }) = false ∧
      checked.target.admitsRepetitionOperand
        (.field { target with id := 2, name := "Base", repeatableScope := [] }) = false := by
  native_decide

/-- The widened source set: mixing with `CurrentRepetition` does not narrow which numeric source
kinds a repeatable Number target admits, measured against the Kernel on `BaseYear`, `Length`, and
`YearFromDate` beside a repetition operand and each alone
([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)).
The scope rule is the only gate, so `AsideText` — a String on a disjoint repeatable level — is
refused where the same atom on the target's own level is admitted. The temporal row carries a
component the declared format lacks as its own separator, so admission is not merely by kind. -/
example :
    let checked := (operation mixed).toOption.get (by native_decide)
    checked.target.admitsRepetitionOperand (.baseYear 2020) = true ∧
      checked.target.admitsRepetitionOperand (.stringLength { id := 6 }) = true ∧
      checked.target.admitsRepetitionOperand (.stringLength { id := 7 }) = false ∧
      checked.target.admitsRepetitionOperand
        (.temporalFieldPart { id := 8, kind := .date, components := dateComponents }
          (.date .year)) = true ∧
      checked.target.admitsRepetitionOperand
        (.temporalFieldPart { id := 8, kind := .date, components := dateComponents }
          (.time .hour)) = false := by
  native_decide

/-- The widened set is reachable from the authored surface, not only from the admission predicate.
Each row resolves a surface atom against the target's own declaring group, so a source in the
target's row elaborates where the nonrepeatable scalar resolver would have refused it. The
`AsideText` row is the separator: same atom shape, disjoint repeatable level, refused. -/
example :
    let len : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .relative 0, groups := [], field := "Text" })
    let asideLen : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .absolute, groups := asidePath, field := "AsideText" })
    let year : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.temporalFieldPart { base := .relative 0, groups := [], field := "When" } (.date .year))
    (operation (.binary .add (repetition innerPath) len)).isOk = true ∧
      (operation (.binary .add (repetition innerPath) (.atom .baseYear))).isOk = true ∧
      (operation (.binary .add (repetition innerPath) year)).isOk = true ∧
      (operation (.binary .add (repetition innerPath) asideLen)).isOk = false := by
  native_decide

/-- Each widened kind also **evaluates** in a row, so the arms added to the operand reader are
exercised rather than merely reachable. One read serves every source by field id: `Text` carries
four UTF-16 units, `When` carries 2021, and the repetition coordinate at `[(10, 2), (20, 3)]` is 3.
The Base Year row reads no cell at all, which is why it is the one kind with no scope to bind. -/
private def readTyped (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  .ok (if address.field == 6 then
      textDecl.checkRaw (.parsed (.str "abcd"))
    else if address.field == 8 then
      whenDecl.checkRaw (.parsed (.temporal (.date {
        instant := { epochMillis := 0 }
        parts := { year := 2021, month := 6, day := 1 }
        basis := .storedGregorian })))
    else target.checkRaw (.parsed (.num 9)))

example :
    let len : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .relative 0, groups := [], field := "Text" })
    let year : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.temporalFieldPart { base := .relative 0, groups := [], field := "When" } (.date .year))
    let run (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((operation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead readTyped [(10, 2), (20, 3)]).toOption)
    run (.binary .add (repetition innerPath) len) = some (.value 7) ∧
      run (.binary .add (repetition innerPath) (.atom .baseYear)) = some (.value 2023) ∧
      run (.binary .add (repetition innerPath) year) = some (.value 2024) := by
  native_decide

private def poisonBeforeMissingBinding (reverse : Bool) : Option (Sum EnvBindingError NumericComputationResult) := do
  let expression := if reverse then .binary .add (repetition innerPath) scalar
    else .binary .add scalar (repetition innerPath)
  let checked ← (operation expression).toOption
  match checked.evaluateAtEnvironmentWithRead
      (fun _ => .ok (target.checkRaw (.rejected .malformed))) [] with
  | .ok value => some (.inr value)
  | .error (.environment error) => some (.inl error)
  | .error _ => none

example : poisonBeforeMissingBinding false = some (.inr (.poison .malformed)) ∧
    poisonBeforeMissingBinding true = some (.inl (.missingBinding 10)) := by native_decide

example : evaluate? (.abs (repetition fixedPath)) [(10, 2), (20, 3)] =
    some (.inr (.value 1)) := by native_decide

example :
    let fractional := AuthoredNumericExpr.binary .multiply (repetition innerPath)
      (.literal { value := 3 / 2, authoredScale := 1 })
    (checkAddressedRepetitionComputation model innerPath 1 fractional).isOk = false ∧
      (checkAddressedRepetitionComputation model innerPath 1 fractional true).isOk = true := by
  native_decide

end A12Kernel.Conformance.AddressedRepetitionComputation
