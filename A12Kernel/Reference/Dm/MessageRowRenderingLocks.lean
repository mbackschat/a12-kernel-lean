import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.ValidationMessageRendering
import A12Kernel.Reference.Dm.GeneratedComputationRule

/-! # Reader-to-render locks for the row a message parameter reads

Each rule of the retained runtime capture
`evidence/kernel-30.8.1/captures/message-parameter-rows-2026-10-13/` is checked by the DM reader, run
by the evaluator on the capture's document, and its template rendered at every firing row's
environment; the texts are the capture's own, identical under both Kernel strategies
([checkpoint](../../../docs/sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15)).
The model below is the capture's topology with only the groups these rules read.

Display text is caller-supplied, so `inputs` reads each cell's stored text, with `0` for an empty
Number, which is what these unlabelled String, Enumeration and scale-0 Number fields render. What the
locks separate is the row: a wrong account reading the firing row's coordinate for an enclosing,
partner or keyed read renders a different capture text.
-/

namespace A12Kernel.Dm.MessageRowRenderingLocks

open Lean A12Kernel

private def string (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl :=
  { id, name, groupPath := group, repeatableScope := scope, policy := { kind := .string } }

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl :=
  { id, name, groupPath := group, repeatableScope := scope
    policy := { kind := .number { scale := 0, signed := true } } }

private def enumeration (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel) (categories : List EnumerationCategoryDeclaration := []) :
    FlatFieldDecl :=
  { id, name, groupPath := group, repeatableScope := scope, policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["A", "B"], categories } }

private def model : FlatModel := {
  fields := [
    string 1 "Anchor" ["Kp"] [], string 2 "Pick" ["Kp"] [],
    string 3 "Key" ["Kp", "Rows"] [10], string 4 "Base" ["Kp", "Rows"] [10],
    string 5 "Gate" ["Kp", "Rows"] [10],
    enumeration 6 "Status" ["Kp", "Rows"] [10] [{ name := "Band", tokens := ["Hi", "Lo"] }],
    string 7 "SubV" ["Kp", "Rows", "Sub"] [10, 11],
    enumeration 8 "Grade" ["Kp", "GA"] [20], string 9 "GNote" ["Kp", "GA"] [20],
    enumeration 10 "Grade" ["Kp", "GB"] [30], number 11 "GVal2" ["Kp", "GB"] [30],
    number 12 "Num" ["Kp", "NRows"] [40], string 13 "V" ["Kp", "NRows"] [40],
    number 14 "RA" ["Kp", "Rows"] [10], number 15 "RT" ["Kp", "Rows"] [10]]
  repeatableGroups := [
    { level := 10, path := ["Kp", "Rows"], repeatability := some 5, indexField := some 3 },
    { level := 11, path := ["Kp", "Rows", "Sub"], repeatability := some 3 },
    { level := 20, path := ["Kp", "GA"], repeatability := some 5, indexField := some 8 },
    { level := 30, path := ["Kp", "GB"], repeatability := some 5, indexField := some 10 },
    { level := 40, path := ["Kp", "NRows"], repeatability := some 3, indexField := some 12 }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def world : World := { now := { epochMillis := 0 } }

private def row (cells : List (String × String)) (members : List (String × Json) := []) : Json :=
  .mkObj (cells.map (fun (name, value) => (name, Json.str value)) ++ members)

/-- The capture's document, without the groups no rule here reads, with the computation capture's
`RA` and `RT` values merged into its `Rows`, which no other rule here reads. -/
private def documentJson : Json :=
  .mkObj [("Kp", .mkObj [
    ("Anchor", .str "a"), ("Pick", .str "k0"),
    ("Rows", .arr #[
      row [("Key", "k0"), ("Base", "b0"), ("Status", "A"), ("RA", "2"), ("RT", "4")],
      row [("Key", "k1"), ("Base", "b1"), ("Status", "B"), ("RA", "3"), ("RT", "7")]
        [("Sub", .arr #[row [("SubV", "s1")], row [("SubV", "s2")]])],
      row [("Key", "k2"), ("Status", "A"), ("RA", "5"), ("RT", "1")]]),
    ("GA", .arr #[row [("Grade", "A"), ("GNote", "n1")], row [("Grade", "B"), ("GNote", "n2")]]),
    ("GB", .arr #[row [("Grade", "B"), ("GVal2", "7")], row [("Grade", "A"), ("GVal2", "5")]]),
    ("NRows", .arr #[row [("Num", "1"), ("V", "v1")], row [("Num", "2"), ("V", "v2")]])])]

private def inputs (document : Document) : ValidationMessageInputs := {
  fieldName := fun field => {
    providerResult := none, modelLabel := none
    debugDisplay := ((model.fields.find? (·.id == field)).map (·.name)).getD "" }
  fieldValue := fun cell => {
    displayValue := document.rawCells cell
    defaultDisplay := if [11, 12, 14, 15].contains cell.field then "0" else "" }
  fieldStoredToken := document.rawCells
  formPointer := fun _ _ => "" }

private def rule (group : GroupPath) (name errorEntity condition : String) : DmRule :=
  { group, name, errorCode := name, severity := "ERROR", errorEntityRelPath := errorEntity, condition }

private def outcome : Except ValidationMessageRenderingError (List String) →
    Sum ValidationMessageRenderingError (List String)
  | .ok texts => .inr texts
  | .error error => .inl error

/-- Every firing's rendered text, in evaluation order, or the first rendering error. -/
private def rendered (definition : DmRule) (template : String) :
    Option (Sum ValidationMessageRenderingError (List String)) := do
  let input ← (readDocument dm documentJson).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  let references ← preliminary.messageReferenceInputs.toOption
  let document := input.data.toDocument
  let render {condition : ValidationMessageCondition model}
      (template : CheckedValidationMessageTemplate model condition) (environment : Env) :=
    let context : ValidationMessageRowContext model builtinStringPatternCompiler := {
      environment, document, prepared, locale := "en_US", references := some references }
    (template.toRenderPlanAt context (inputs document)).map (·.render.text)
  match ← (checkValidationRule dm .english definition).toOption with
  | .ordinary checkedRule =>
      let template ← (elaborateValidationMessageTemplate model .english (.rule checkedRule)
        template).toOption
      let fired ← (runRuleAt world checked checkedRule).toOption
      pure (outcome (fired.mapM fun (environment, _) => render template environment))
  | .parallel parallelRule =>
      let template ← (elaborateValidationMessageTemplate model .english
        (.parallel parallelRule definition.group) template).toOption
      let rows ← (parallelRule.evalDocument preliminary preliminary.messageCacheContext.toOption).toOption
      pure (outcome ((rows.filter (·.outcome.message?.isSome)).mapM fun fired =>
        render template fired.row.messageEnvironment))

example : model.validate.isOk = true := by native_decide

/-- Field values, categories and the index token read the firing row's own cells; a third row
lacking `Base` does not fire. -/
example : rendered (rule ["Kp", "Rows"] "RRow" "../Base"
      "FieldFilled(Base) And FieldFilled(Status) And FieldNotFilled(Gate)")
      "b=[$Base.value$] n=[$Base$] st=[$Status.value$] cat=[$Status->Band$] g=[$Gate.value$] i=[$index(Key).value$]" =
    some (.inr ["b=[b0] n=[Base] st=[A] cat=[Hi] g=[] i=[k0]",
      "b=[b1] n=[Base] st=[B] cat=[Lo] g=[] i=[k1]"]) := by native_decide

/-- An enclosing row's field renders that row, while the group shorthands render each level's own
coordinate. -/
example : rendered (rule ["Kp", "Rows", "Sub"] "RSub" "../SubV" "FieldFilled(SubV) And FieldFilled(../Base)")
      "sub=[$SubV.value$] outer=[$../Base.value$] own=[$#RuleGroup$] up=[$#/Kp/Rows$]" =
    some (.inr ["sub=[s1] outer=[b1] own=[1] up=[2]", "sub=[s2] outer=[b1] own=[2] up=[2]"]) := by
  native_decide

/-- A partner group's field renders the row the join pairs with the firing row, `Grade` `A` with the
second `GB` row; the firing row's coordinate would render the other value. -/
example : rendered (rule ["Kp", "GA"] "RPar" "../GNote" "FieldFilled(GNote) And FieldFilled(/Kp/GB/GVal2)")
      "p=[$/Kp/GB/GVal2.value$] own=[$GNote.value$] pn=[$/Kp/GB/GVal2$]" =
    some (.inr ["p=[5] own=[n1] pn=[GVal2]", "p=[7] own=[n2] pn=[GVal2]"]) := by native_decide

/-- A keyed parameter renders the row its key selects: a literal, the group's index field, a field-valued
key read at its own cell, and a Number index read by value. -/
example : rendered (rule ["Kp"] "RKey" "../Anchor" "FieldFilled(Anchor) And FieldFilled(/Kp/Rows/Base For \"k1\")")
      "kb=[$/Kp/Rows/Base.value For \"k1\"$] kk=[$/Kp/Rows/Key.value For \"k1\"$] kn=[$/Kp/Rows/Base For \"k1\"$] a=[$Anchor.value$]" =
      some (.inr ["kb=[b1] kk=[k1] kn=[Base] a=[a]"]) ∧
    rendered (rule ["Kp"] "RFk" "../Pick" "FieldFilled(Pick) And FieldFilled(/Kp/Rows/Base For Pick)")
      "f=[$/Kp/Rows/Base.value For Pick$] fk=[$/Kp/Rows/Key.value For Pick$]" =
      some (.inr ["f=[b0] fk=[k0]"]) ∧
    rendered (rule ["Kp"] "RNum" "../Anchor" "FieldFilled(Anchor) And FieldFilled(/Kp/NRows/V For \"2\")")
      "nv=[$/Kp/NRows/V.value For \"2\"$] nk=[$/Kp/NRows/Num.value For \"2\"$] ng=[$#/Kp/NRows For \"2\"$]" =
      some (.inr ["nv=[v2] nk=[2] ng=[2]"]) := by native_decide

/-- A selected row's empty cell renders empty, and its category and value read that row. -/
example : rendered (rule ["Kp"] "RK2" "../Anchor"
      "FieldFilled(Anchor) And FieldNotFilled(/Kp/Rows/Base For \"k2\") And FieldFilled(/Kp/Rows/Status For \"k2\")")
      "e=[$/Kp/Rows/Base.value For \"k2\"$] sc=[$/Kp/Rows/Status->Band For \"k2\"$] sv=[$/Kp/Rows/Status.value For \"k2\"$]" =
    some (.inr ["e=[] sc=[Hi] sv=[A]"]) := by native_decide

/-- A key selecting no row fires the rule but faults its rendering, where the Kernel replaces the whole
text with its evaluation-fault text. -/
example : rendered (rule ["Kp"] "RMiss" "../Anchor" "FieldFilled(Anchor) And FieldNotFilled(/Kp/Rows/Base For \"k9\")")
      "m=[$/Kp/Rows/Base.value For \"k9\"$]" = some (.inl .unresolvedSelection) := by native_decide

/-- A computation's message is its generated rule's: it fires only on the filled row whose holding
alternative disagrees, the second, and renders that row's cells and coordinate
(`evidence/kernel-30.8.1/captures/computation-message-members-2026-10-13/`). -/
private def computation : DmComputation where
  group := ["Kp", "Rows"]
  name := "RTComp"
  targetRelPath := "../RT"
  commonPrecondition := none
  errorCodesToSuppress := []
  alternatives := [{ precondition := some "FieldFilled(Base)", operation := "[RA] * 2" }]

example : (computation.generatedRule? .english).bind (rendered ·
      "row=[$#RuleGroup$] t=[$RT.value$] a=[$RA.value$] b=[$Base.value$] i=[$index(Key).value$] up=[$#RootGroup$]") =
    some (.inr ["row=[2] t=[7] a=[3] b=[b1] i=[k1] up=[1]"]) := by native_decide

end A12Kernel.Dm.MessageRowRenderingLocks
