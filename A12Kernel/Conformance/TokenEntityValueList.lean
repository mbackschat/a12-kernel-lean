import A12Kernel.Elaboration.TokenEntityValueList
import A12Kernel.Elaboration.TokenDistinctCount

/-! # Checked mixed String entity-list value-list locks -/

namespace A12Kernel.Conformance.TokenEntityValueList

open A12Kernel

private def matchField : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Match"
    policy := { kind := .string } }

private def needleField : FlatFieldDecl :=
  { matchField with id := 2, name := "Needle" }

private def spareField : FlatFieldDecl :=
  { matchField with id := 3, name := "Spare" }

private def repeatedField : FlatFieldDecl :=
  { matchField with
    id := 4
    groupPath := ["Form", "Rows"]
    name := "Code"
    stringPolicy := { lineBreaksPermitted := true }
    repeatableScope := [10] }

private def otherRepeatedField : FlatFieldDecl :=
  { repeatedField with id := 5, name := "OtherCode" }

private def nestedField : FlatFieldDecl :=
  { matchField with
    id := 6
    groupPath := ["Form", "Rows", "Details"]
    name := "NestedCode"
    repeatableScope := [10, 20] }

private def enumField : FlatFieldDecl :=
  { id := 7, groupPath := ["Form"], name := "Choice"
    policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["A", "B"] } }

private def otherEnumField : FlatFieldDecl :=
  { enumField with id := 8, name := "OtherChoice" }

private def model : FlatModel :=
  { fields := [
      matchField, needleField, spareField, repeatedField, otherRepeatedField,
      nestedField, enumField, otherEnumField]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Details"],
        repeatability := some 2 }] }

private def world : World := { now := { epochMillis := 0 } }

private def direct (name : String) : SurfaceTokenEntityOperand :=
  .field { base := .absolute, groups := ["Form"], field := name }

private def star (name : String := "Code") : SurfaceTokenEntityOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := name }

private def nestedChildStar : SurfaceTokenEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows" },
      { name := "Details", starred := true }]
    field := "NestedCode" }

private def nestedAllStar : SurfaceTokenEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true },
      { name := "Details", starred := true }]
    field := "NestedCode" }

private def rowsPath : SurfaceGroupPath :=
  { base := .absolute, groups := ["Form", "Rows"] }

private def falseHaving : SurfaceCorrelatedHaving :=
  .compareRepetitions .less
    { origin := .inner, group := .path rowsPath }
    { origin := .inner, group := .path rowsPath }

private def filteredStar : SurfaceTokenEntityOperand :=
  .starHaving {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Code" } falseHaving

private def entitySource (first : SurfaceTokenEntityOperand)
    (rest : List SurfaceTokenEntityOperand) : SurfaceTokenEntitySource :=
  { first, rest }

private def authored (quantifier : ValueListQuantifier)
    (fields values : SurfaceTokenEntitySource) :
    SurfaceTokenEntityValueListSource :=
  { quantifier, fields, values }

private def values : SurfaceTokenEntitySource :=
  entitySource (direct "Needle") [direct "Spare"]

private def row1 : RowAddr := { group := 10, path := [1] }
private def row2 : RowAddr := { group := 10, path := [2] }
private def detail11 : RowAddr := { group := 20, path := [1, 1] }
private def detail12 : RowAddr := { group := 20, path := [1, 2] }
private def detail21 : RowAddr := { group := 20, path := [2, 1] }

private inductive RepeatedFixture where
  | other
  | presentEmpty
  | malformed

private def RepeatedFixture.stored : RepeatedFixture → String
  | .other => "OTHER"
  | .presentEmpty => ""
  | .malformed => "bad"

private def RepeatedFixture.raw : RepeatedFixture → RawCell
  | .other => .parsed (.str "OTHER")
  | .presentEmpty => .presentEmpty
  | .malformed => .rejected .malformed

private def data (repeated : RepeatedFixture) : DocumentData :=
  { instantiatedRows := [row1]
    cells := [
      { address := { field := 1, path := [] }
        stored := "MATCH", raw := .parsed (.str "MATCH") },
      { address := { field := 2, path := [] }
        stored := "MATCH", raw := .parsed (.str "MATCH") },
      { address := { field := 3, path := [] }
        stored := "SPARE", raw := .parsed (.str "SPARE") },
      { address := { field := 4, path := [1] }
        stored := repeated.stored, raw := repeated.raw }] }

private def multipleStarData : DocumentData :=
  { instantiatedRows := [detail21, row2, detail12, row1, detail11]
    cells := [
      { address := { field := 1, path := [] }
        stored := "MATCH", raw := .parsed (.str "MATCH") },
      { address := { field := 2, path := [] }
        stored := "MATCH", raw := .parsed (.str "MATCH") },
      { address := { field := 3, path := [] }
        stored := "SPARE", raw := .parsed (.str "SPARE") },
      { address := { field := 4, path := [1] }
        stored := "A\r\nB", raw := .parsed (.str "A\r\nB") },
      { address := { field := 4, path := [2] }
        stored := "SECOND", raw := .parsed (.str "SECOND") },
      { address := { field := 5, path := [1] }
        stored := "MATCH", raw := .parsed (.str "MATCH") },
      { address := { field := 5, path := [2] }
        stored := "OTHER", raw := .parsed (.str "OTHER") },
      { address := { field := 6, path := [1, 1] }
        stored := "N11", raw := .parsed (.str "N11") },
      { address := { field := 6, path := [1, 2] }
        stored := "N12", raw := .parsed (.str "N12") },
      { address := { field := 6, path := [2, 1] }
        stored := "N21", raw := .parsed (.str "N21") }] }

private def checkedDocument? (source : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" source).toOption

private inductive Snapshot where
  | verdict (verdict : Verdict)
  | structural (cause : CheckedAddressingError)
  | elaboration
  deriving Repr, DecidableEq

private def fullSnapshot (surface : SurfaceTokenEntityValueListSource)
    (source : DocumentData) (outer : Env := []) : Snapshot :=
  match elaborateTokenEntityValueListSource model ["Form"] surface with
  | .error _ => .elaboration
  | .ok checked =>
      match checkedDocument? source with
      | none => .elaboration
      | some document =>
          match checked.evaluateFull document outer with
          | .ok verdict => .verdict verdict
          | .error cause => .structural cause

private def relevance (path : List String)
    (indices : List RelevanceIndex) : RelevantEntityPattern :=
  { path, indices }

private def directOnlyScope : ValidationRelevanceScope :=
  .partialSet [
    relevance matchField.path [.concrete 1, .concrete 1],
    relevance needleField.path [.concrete 1, .concrete 1],
    relevance spareField.path [.concrete 1, .concrete 1]]

private def codeOnlyScope : ValidationRelevanceScope :=
  .partialSet [
    relevance repeatedField.path [.concrete 1, .all, .concrete 1],
    relevance needleField.path [.concrete 1, .concrete 1],
    relevance spareField.path [.concrete 1, .concrete 1]]

private def partialSnapshot (surface : SurfaceTokenEntityValueListSource)
    (source : DocumentData) (scope : ValidationRelevanceScope) : Snapshot :=
  match elaborateTokenEntityValueListSource model ["Form"] surface with
  | .error _ => .elaboration
  | .ok checked =>
      match checkedDocument? source with
      | none => .elaboration
      | some document =>
          match checked.evaluatePartial document [] scope with
          | .ok (.evaluated verdict) => .verdict verdict
          | .ok .skippedHaving => .elaboration
          | .error cause => .structural cause

/- A fields-side `No` match hides a later semantic UNKNOWN, while reversing the same String operands exposes it. -/
example :
    fullSnapshot
        (authored .no (entitySource (direct "Match") [star]) values)
        (data .malformed) = .verdict .notFired ∧
      fullSnapshot
        (authored .no (entitySource star [direct "Match"]) values)
        (data .malformed) = .verdict .unknown := by
  native_decide

/- A filtered nonwitness before an unfiltered String witness does not escalate the deciding match to OMISSION. -/
example :
    fullSnapshot
        (authored .atLeastOne
          (entitySource filteredStar [direct "Match"]) values)
        (data .other) = .verdict (.fired .value) := by
  native_decide

/- Partial nonrelevance remains attached to its authored String operand position. -/
example :
    partialSnapshot
        (authored .no
          (entitySource (direct "Match") [star]) values)
        (data .other) directOnlyScope = .verdict .notFired ∧
      partialSnapshot
        (authored .no
          (entitySource star [direct "Match"]) values)
        (data .other) directOnlyScope = .verdict .unknown := by
  native_decide

/- Two independently starred String operands retain positional partial relevance. -/
example :
    partialSnapshot
        (authored .no
          (entitySource (star "Code") [star "OtherCode"]) values)
        multipleStarData codeOnlyScope = .verdict .unknown := by
  native_decide

private def checkedDocumentDistinctCount : Option NumericOperand := do
  let checked ←
    (elaborateTokenEntitySource model ["Form"]
      (entitySource (star "Code") [star "OtherCode"])).toOption
  let document ← checkedDocument? multipleStarData
  (checked.evaluateCheckedDocumentDistinctValidation document []).toOption

/- The second token consumer obtains both independently starred String operands from the same rich checked construction, then retains its distinct-count first-cause scan and exact-token fold. -/
example : checkedDocumentDistinctCount = some (.value 4 .fixed) := by
  native_decide

/- A missing fixed outer binding is a structural addressing failure, never semantic UNKNOWN. -/
example :
    fullSnapshot
        (authored .no
          (entitySource nestedChildStar [direct "Match"]) values)
        { instantiatedRows := [], cells := (data .presentEmpty).cells.take 3 } =
      .structural (.addressing (.missingBinding 10)) := by
  native_decide

/- Field-valued sides cannot mix String and Enumeration base families even though distinct-count consumers share the wider token entity-list owner. -/
example :
    fullSnapshot
        (authored .atLeastOne
          (entitySource (direct "Match") [direct "Needle"])
          (entitySource (direct "Choice") [direct "OtherChoice"]))
        (data .other) = .elaboration := by
  native_decide

private inductive ProjectedToken where
  | present (value : String)
  | empty
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

private def projectedToken : ValueListCell .token → ProjectedToken
  | .present value => .present value
  | .empty => .empty
  | .unknown cause => .unknown cause

private structure OperandView where
  field : FieldId
  topology : Option (List Env)
  openTail : Bool
  addressed : List (CellAddr × Option String)
  projected : List ProjectedToken
  deriving Repr, DecidableEq

private def sourceField :
    CheckedTokenEntityOperand model → FieldId
  | .field source => source.operand.field.id
  | .star source => source.operand.field.id

private def operandView
    (resolved : ResolvedCheckedTokenEntityOperand model) : OperandView :=
  { field := sourceField resolved.source
    topology := resolved.topology.map (·.environments)
    openTail := resolved.hasUninstantiatedTail
    addressed := resolved.addressedCells.map fun cell =>
      (cell.address, cell.stored)
    projected :=
      (resolved.valueListSideAt .validation).cells.map projectedToken }

private structure ConsumerView where
  family : TokenEntityValueListFamily
  fields : List OperandView
  values : List OperandView
  verdict : Verdict
  deriving Repr, DecidableEq

private inductive ConsumerQuery where
  | storedString (surface : SurfaceTokenEntityValueListSource)
      (source : DocumentData)
  | projectedEnumeration

private inductive ConsumerResult where
  | available (view : ConsumerView)
  | structural (cause : CheckedAddressingError)
  | rejected
  | insufficientInformation
  deriving Repr, DecidableEq

/-- Same-context Execute/Transform/Explain probe: execute the public checked route, traverse source-preserving operands, and explain topology, exact stored payload, and declaration-owned evaluated tokens. Projection-bearing Enumeration authoring remains explicit insufficient information at this surface. -/
private def inspectForConsumer : ConsumerQuery → ConsumerResult
  | .projectedEnumeration => .insufficientInformation
  | .storedString surface source =>
      match elaborateTokenEntityValueListSource model ["Form"] surface with
      | .error _ => .rejected
      | .ok checked =>
          match checkedDocument? source with
          | none => .rejected
          | some document =>
              match checked.resolveFull document [] with
              | .error cause => .structural cause
              | .ok resolved =>
                  .available {
                    family := resolved.family
                    fields := resolved.fields.map operandView
                    values := resolved.values.map operandView
                    verdict := resolved.evaluate }

/- Nested and outer String stars preserve independent canonical environments, hierarchical extent, exact stored CRLF spelling, normalized evaluated text, and authored order. -/
example :
    inspectForConsumer (.storedString
      (authored .atLeastOne
        (entitySource nestedAllStar [star]) values)
      multipleStarData) =
      .available {
        family := .string
        fields := [
          { field := 6
            topology := some [
              [(10, 1), (20, 1)],
              [(10, 1), (20, 2)],
              [(10, 2), (20, 1)]]
            openTail := true
            addressed := [
              ({ field := 6, path := [1, 1] }, some "N11"),
              ({ field := 6, path := [1, 2] }, some "N12"),
              ({ field := 6, path := [2, 1] }, some "N21")]
            projected := [
              .present "N11", .present "N12", .present "N21"] },
          { field := 4
            topology := some [[(10, 1)], [(10, 2)]]
            openTail := false
            addressed := [
              ({ field := 4, path := [1] }, some "A\r\nB"),
              ({ field := 4, path := [2] }, some "SECOND")]
            projected := [.present "A\nB", .present "SECOND"] }]
        values := [
          { field := 2
            topology := none
            openTail := false
            addressed := [({ field := 2, path := [] }, some "MATCH")]
            projected := [.present "MATCH"] },
          { field := 3
            topology := none
            openTail := false
            addressed := [({ field := 3, path := [] }, some "SPARE")]
            projected := [.present "SPARE"] }]
        verdict := .notFired } ∧
      inspectForConsumer .projectedEnumeration =
        .insufficientInformation := by
  native_decide

end A12Kernel.Conformance.TokenEntityValueList
