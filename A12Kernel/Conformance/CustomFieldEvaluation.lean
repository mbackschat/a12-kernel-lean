import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.Conformance.CustomFieldEvaluation — checked custom full-evaluation locks -/

namespace A12Kernel.Conformance.CustomFieldEvaluation

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def validator : RegisteredCustomFieldValidator := fun value context =>
  if value == "accepted" && context.locale == "en_US" then none else some rejection

private def worldWithValidator : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def emptyWorld : World :=
  { now := { epochMillis := 0 } }

private def compilePattern : StringPatternCompiler := fun source =>
  if source == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def code : FlatFieldDecl :=
  {
    id := 1
    groupPath := ["Order"]
    name := "Code"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def ordinary : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "Note",
    policy := { kind := .string } }

private def patterned : FlatFieldDecl :=
  {
    id := 4
    groupPath := ["Order"]
    name := "Patterned"
    policy := { kind := .string }
    stringPatternSource := some "A+"
  }

private def invalidCustomNumber : FlatFieldDecl :=
  {
    id := 3
    groupPath := ["Order"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := true } }
    customType := some { name := "ProjectCode" }
  }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawAt (id : FieldId) (cell : RawCell) : RawFlatContext where
  read candidate := if candidate == id then cell else .empty

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read candidate :=
    if candidate == leftId then left
    else if candidate == rightId then right
    else .empty

private def outcome (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) :
    Except FlatStringContextEvaluationError Verdict :=
  elaborateAndEvalFull compilePattern locale model world
    ["Order"] raw true condition

private def verdictOf (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) : Option Verdict :=
  match outcome model world locale raw condition with
  | .ok verdict => some verdict
  | .error _ => none

private def errorOf (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) :
    Option FlatStringContextEvaluationError :=
  match outcome model world locale raw condition with
  | .ok _ => none
  | .error error => some error

private def unpreparedVerdict (model : FlatModel) (world : World)
    (raw : RawFlatContext) (condition : SurfaceCondition) : Option Verdict :=
  match elaborateAndEvalUnpreparedFull model world ["Order"] raw true condition with
  | .ok verdict => some verdict
  | .error _ => none

/- Accepted, rejected, and empty custom fields flow through one prepared checked context. -/
example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id (.parsed (.str "accepted"))) (.fieldFilled (path "Code")) =
    some (.fired .value) := by
  native_decide

example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id (.parsed (.str "rejected"))) (.fieldFilled (path "Code")) =
    some .unknown := by
  native_decide

example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id .empty) (.fieldFilled (path "Code")) =
    some .notFired := by
  native_decide

/- Ordinary no-custom models retain their existing full-evaluation result. -/
example : verdictOf { fields := [ordinary] } emptyWorld "en_US"
    (rawAt ordinary.id (.parsed (.str "note")))
    (.fieldFilled (path "Note")) = some (.fired .value) := by
  native_decide

/- A prepared custom entry point must not bypass an ordinary declared pattern on another field. -/
example : verdictOf { fields := [patterned] } emptyWorld "en_US"
    (rawAt patterned.id (.parsed (.str "BBB")))
    (.fieldFilled (path "Patterned")) = some .unknown := by
  native_decide

example : unpreparedVerdict { fields := [patterned] } emptyWorld
    (rawAt patterned.id (.parsed (.str "BBB")))
    (.fieldFilled (path "Patterned")) = some .unknown := by
  native_decide

example : verdictOf { fields := [patterned] } emptyWorld "en_US"
    (rawAt patterned.id (.parsed (.str "AAA")))
    (.fieldFilled (path "Patterned")) = some (.fired .value) := by
  native_decide

/- One mixed row dispatches the ordinary pattern and registered custom fields through their distinct prepared checkers before the shared condition tree. -/
example : verdictOf { fields := [patterned, code] } worldWithValidator "en_US"
    (rawPair patterned.id (.parsed (.str "AAA"))
      code.id (.parsed (.str "accepted")))
    (.and (.fieldFilled (path "Patterned")) (.fieldFilled (path "Code"))) =
      some (.fired .value) := by
  native_decide

example : verdictOf { fields := [patterned, code] } worldWithValidator "en_US"
    (rawPair patterned.id (.parsed (.str "BBB"))
      code.id (.parsed (.str "accepted")))
    (.and (.fieldFilled (path "Patterned")) (.fieldFilled (path "Code"))) =
      some .unknown := by
  native_decide

/- Preparation and condition elaboration failures remain distinct. -/
example : errorOf { fields := [code] } emptyWorld "en_US"
    (rawAt code.id (.parsed (.str "accepted"))) (.fieldFilled (path "Code")) =
    some (.preparation (.custom (.missingValidator "ProjectCode"))) := by
  native_decide

example : errorOf { fields := [invalidCustomNumber] } worldWithValidator "en_US"
    (rawAt invalidCustomNumber.id (.parsed (.num 1)))
    (.fieldFilled (path "Count")) =
    some (.preparation (.model
      (.customTypeRequiresString ["Order", "Count"]))) := by
  native_decide

example : errorOf { fields := [ordinary] } emptyWorld "en_US"
    (rawAt ordinary.id (.parsed (.str "note")))
    (.fieldFilled (path "Missing")) =
    some (.condition (.resolve (.invalidEntity (path "Missing")))) := by
  native_decide

end A12Kernel.Conformance.CustomFieldEvaluation
