import Lean.Data.Json
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # Retained field-declaration notifications through the reader

Each row of the retained capture patches a base model, and the Kernel's whole-model check reports a
multiset of `(class, element)` notifications for the result. A row agrees when the reader's aggregation
of the field-type, element-name, group, rule-name and element-text laws reports, restricted to the
vocabulary those laws own (`declarationNotificationVocabulary`), exactly the multiset the Kernel
reported restricted to the same vocabulary. The capture also records the classes of rule conditions and
computation operations; those are other owners' and are outside the comparison, so a row's agreement
says nothing about them.

An observed notification whose element is null matches a reported one of the same class at any element:
the Kernel names no element for a name holding a `/`, whose path it cannot form.

A row of `deferred` is skipped and counted. Both the capture and the base model load through
`parseModelJson`, which keeps a lone surrogate visible.
-/

namespace A12Kernel.Evidence.DeclarationNotificationProjection

open Lean A12Kernel A12Kernel.Dm

/-- The capture, under the evidence root. -/
def captureDirectory : System.FilePath := "captures/field-declaration-notifications-2026-10-13"

/-- Rows whose reported classes depend on a class this projection does not own, each with the reason.
A row stays out only when the laws disagree with it for that reason alone; no other row disagrees. -/
def deferred : List (String × String) := []

private def readJson (path : System.FilePath) : IO Json := do
  match parseModelJson (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

private def modifyMember (json : Json) (key : String) (change : Json → Json) : Json :=
  json.setObjVal! key (change (json.getObjValD key))

private def extend (json : Json) (extra : Array Json) : Json :=
  match json with
  | .arr items => .arr (items ++ extra)
  | _ => .arr extra

/-- A row's patch applied to the base model: elements appended to the first root group, root groups
added, the declared locales and the type definitions replaced, the condition language set. -/
private def applyPatch (base patch : Json) : Json :=
  let array (key : String) := (patch.getObjValAs? (Array Json) key).toOption.getD #[]
  let appended := modifyMember base "content" fun content =>
    modifyMember content "modelRoot" fun root =>
      modifyMember root "rootGroups" fun groups =>
        match groups with
        | .arr items =>
            .arr ((items.modify 0 fun form => modifyMember form "Group" fun group =>
              modifyMember group "elements" (extend · (array "append"))) ++ array "roots")
        | other => other
  let located := match (patch.getObjValAs? (Array String) "locales").toOption with
    | some codes => modifyMember appended "header" fun header =>
        header.setObjVal! "locales" (.arr (codes.map fun code => Json.mkObj [("code", .str code)]))
    | none => appended
  let defined := match patch.getObjVal? "typeDefinitions" with
    | .ok definitions => modifyMember located "content" (·.setObjVal! "typeDefinitions" definitions)
    | .error _ => located
  match (patch.getObjValAs? String "language").toOption with
  | some code => modifyMember defined "content" fun content =>
      modifyMember content "modelConfig" fun config =>
        config.setObjVal! "conditionLanguage" (Json.mkObj [("code", .str code)])
  | none => defined

/-- The Java compilation decisions the capture's pattern rows retain: `(` does not compile and every
other source does. -/
private def capturedJavaCompilation : StringPatternCompiler :=
  fun source => if source == "(" then none else some fun _ => true

private def entry (label at_ : String) : String := s!"{label} at {at_}"

private def sorted (entries : List String) : List String := entries.mergeSort (· ≤ ·)

/-- The Kernel's notifications of an observation, restricted to the vocabulary the laws own, each with
its element or none. -/
private def observed (observation : Json) : List (String × Option String) :=
  ((observation.getObjValAs? (Array Json) "notifications").toOption.getD #[]).toList.filterMap
    fun notification => do
      let code ← (notification.getObjValAs? String "code").toOption
      if !declarationNotificationVocabulary.contains code then none
      pure (code, (notification.getObjValAs? String "at").toOption)

/-- Whether the reported notifications are exactly the observed ones: those with an element match
exactly, those without match any reported element of their class, and nothing is left over. -/
private def agrees (expected : List (String × Option String)) (reported : List (String × String)) :
    Bool :=
  let located := expected.filterMap fun (code, at_) => at_.map (code, ·)
  let unlocated := expected.filterMap fun (code, at_) => if at_.isNone then some code else none
  let afterLocated := located.foldl (init := some reported) fun remaining item =>
    remaining.bind fun list => if list.contains item then some (list.erase item) else none
  match unlocated.foldl (init := afterLocated) fun remaining code =>
      remaining.bind fun list => (list.findIdx? (·.1 == code)).map list.eraseIdx with
  | some [] => true
  | _ => false

/-- Replay every row and return the agreeing and the deferred row counts. -/
def checkArtifacts (root : System.FilePath) : IO (Nat × Nat) := do
  let directory := root / captureDirectory
  let base ← readJson (directory / "Wh_DM.json")
  let rows := ((← readJson (directory / "rows.json")).getArr?.toOption.getD #[]).toList
  let observations := ((← readJson (directory / "observations.json")).getArr?.toOption.getD #[]).toList
  if rows.isEmpty then throw (IO.userError s!"{captureDirectory}: no rows")
  let mut agreeing := 0
  let mut skipped := 0
  let mut failures : Array String := #[]
  for row in rows do
    let id := (row.getObjValAs? String "id").toOption.getD "?"
    if deferred.any (·.1 == id) then
      skipped := skipped + 1
      continue
    let some observation := observations.find? fun candidate =>
        (candidate.getObjValAs? String "case").toOption == some id
      | failures := failures.push s!"{id}: no observation"; continue
    let model := applyPatch base (row.getObjValD "patch")
    match fieldTypeDeclarationNotifications model (compilePattern := capturedJavaCompilation) with
    | .error reason => failures := failures.push s!"{id}: unreadable model: {reason}"
    | .ok reported =>
        let expected := observed observation
        if agrees expected reported then agreeing := agreeing + 1
        else
          failures := failures.push s!"{id}: expected {sorted (expected.map fun (code, at_) => entry code (at_.getD "-"))} but the laws report {sorted (reported.map fun (label, at_) => entry label at_)}"
  if !failures.isEmpty then
    throw (IO.userError s!"field-declaration notifications diverge:\n{"\n".intercalate failures.toList}")
  pure (agreeing, skipped)

end A12Kernel.Evidence.DeclarationNotificationProjection
