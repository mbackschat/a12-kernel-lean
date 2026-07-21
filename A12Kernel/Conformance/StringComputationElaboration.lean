import A12Kernel.Elaboration.StringComputation

/-! # Checked String-computation expression lowering locks -/

namespace A12Kernel.Conformance.StringComputationElaboration

open A12Kernel

private def source : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Source",
    policy := { kind := .string } }

private def suffix : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Suffix",
    policy := { kind := .string } }

private def amount : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

private def repeatedText : FlatFieldDecl :=
  { id := 3, groupPath := ["Form", "Rows"], name := "Text",
    policy := { kind := .string }, repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [source, suffix, amount, repeatedText]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def coreOf
    (result : Except StringComputationElabError (CheckedStringExpr model)) :
    Option StringExpr :=
  result.toOption.map (·.core)

private def errorOf
    (result : Except StringComputationElabError (CheckedStringExpr model)) :
    Option StringComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def raw (sourceCell suffixCell : RawCell) : RawFlatContext where
  read field :=
    if field = source.id then sourceCell
    else if field = suffix.id then suffixCell
    else .empty

private def storeOf (expression : StringExpr SurfaceFieldPath)
    (input : RawFlatContext) : Option StringStore :=
  match elaborateStringExpr model ["Form"] expression with
  | .error _ => none
  | .ok checked => (checked.evaluate input).toOption

private def normalizedResult : StoredString :=
  { text := "A\nB!", nonempty := by decide }

/- Copy, decoded literal, and concatenation lower structurally without changing encounter order. -/
example :
    coreOf (elaborateStringExpr model ["Form"]
      (.concat
        (.field (absolute ["Form"] "Source"))
        (.concat (.literal "-") (.field (bare "Suffix"))))) =
      some (.concat (.field source.id)
        (.concat (.literal "-") (.field suffix.id))) := by
  native_decide

/- The checked expression delegates to the existing cached String evaluator. -/
example :
    storeOf
      (.concat (.field (bare "Source")) (.literal "!"))
      (raw (.parsed (.str "A\r\nB")) .empty) =
      some (.produced normalizedResult) := by
  native_decide

/- Two empty field contributions remain an evaluated empty concatenation until the root store clears it. -/
example :
    storeOf
      (.concat (.field (bare "Source")) (.field (bare "Suffix")))
      (raw .presentEmpty .empty) = some .noValue := by
  native_decide

/- Raw cells are checked with the same model policy before the runtime tree reads them. -/
example :
    storeOf (.field (bare "Source"))
      (raw (.parsed (.num 7)) .empty) = some (.poison .malformed) := by
  native_decide

/- Wrong-kind and repeatable reads fail before a runtime expression can be constructed. -/
example :
    errorOf (elaborateStringExpr model ["Form"]
        (.field (bare "Amount"))) =
        some (.fieldKindMismatch amount.path .number) ∧
      errorOf (elaborateStringExpr model ["Form"]
        (.field (absolute ["Form", "Rows"] "Text"))) =
        some (.resolve (.repeatableReference repeatedText.path)) := by
  native_decide

end A12Kernel.Conformance.StringComputationElaboration
