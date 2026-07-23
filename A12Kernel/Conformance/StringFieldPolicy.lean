import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StringComputation

/-! # Declaration-owned String formal-policy conformance locks -/

namespace A12Kernel.Conformance.StringFieldPolicy

open A12Kernel

private def stringDeclaration (policy : StringFieldPolicy := {}) : FlatFieldDecl :=
  { id := 1
    groupPath := ["Claim"]
    name := "Note"
    policy := { kind := .string }
    stringPolicy := policy }

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def isStringFieldError (expected : StringFieldError) :
    Except StringFieldError (Option String) → Bool
  | .error actual => actual == expected
  | .ok _ => false

private def isCheckedText (expected : Option String) :
    Except StringFieldError (Option String) → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def isDeclaredConstraintPoison :
    Except StringComputationFault StringTerm → Bool
  | .ok (.poison .declaredConstraint) => true
  | _ => false

/- The raw line-break gate precedes normalization and length. -/
example : isStringFieldError .lineBreak
    (({ maxLength := some 1 } : StringFieldPolicy).checkText "AB\r\nCD") = true := by
  native_decide

/- Permitted CRLF is normalized once before the UTF-16 length checks. -/
example : isCheckedText (some "AB\nCD")
    (({ lineBreaksPermitted := true, maxLength := some 5 } :
      StringFieldPolicy).checkText "AB\r\nCD") = true := by
  native_decide

example : isStringFieldError .tooShort
    (({ lineBreaksPermitted := true, minLength := some 6 } :
      StringFieldPolicy).checkText "AB\r\nCD") = true := by
  native_decide

/- Empty input remains ordinary semantic emptiness even under a positive minimum. -/
example : isCheckedText none
    (({ minLength := some 3 } : StringFieldPolicy).checkText "") = true := by
  native_decide

/- An explicit zero maximum follows the runtime's disabled-bound convention. -/
example : isCheckedText (some "A")
    (({ maxLength := some 0 } : StringFieldPolicy).checkText "A") = true := by
  native_decide

/- Declaration checking feeds both validation and computation through one cached finding. -/
example : (stringDeclaration { maxLength := some 3 }).checkRaw
    (.parsed (.str "TOO-LONG")) = {
      rawPresent := true
      parsed := none
      findings := [.declaredConstraint] } := by
  native_decide

/- The declaration retains pattern source independently of condition-pattern execution. The exact numeric profile is checked at ordinary String ingestion and every other declared pattern remains fail-closed for value consumers until the injected matcher is integrated. -/
example :
    let declaration := {
      (stringDeclaration { maxLength := some 15 }) with
      stringPatternSource := some "[0-9]+" }
    declaration.checkRaw (.parsed (.str "123")) = {
        rawPresent := true
        parsed := some (.str "123")
        findings := [] } ∧
      declaration.checkRaw (.parsed (.str "12A")) = {
        rawPresent := true
        parsed := none
        findings := [.declaredConstraint] } ∧
      declaration.toStringValueField? = some { id := 1 } := by
  native_decide

example :
    let declaration := {
      (stringDeclaration { maxLength := some 15 }) with
      stringPatternSource := some "[0-9]*" }
    declaration.toStringValueField? = none := by
  native_decide

example :
    let declaration := stringDeclaration { maxLength := some 3 }
    let context : FlatContext := {
      read := fun _ => declaration.checkRaw (.parsed (.str "TOO-LONG")) }
    (FlatCondition.compare (.string .equal { id := 1 } "TOO-LONG")).evalFull
        context true = .unknown := by
  native_decide

example :
    let declaration := stringDeclaration { maxLength := some 3 }
    let context : FlatContext := {
      read := fun _ => declaration.checkRaw (.parsed (.str "TOO-LONG")) }
    isDeclaredConstraintPoison
      ((StringExpr.field 1).eval { read := context.read }) = true := by
  native_decide

/- The general repeatable checked context must not bypass declaration-owned String policy. -/
example :
    let declaration : FlatFieldDecl := {
      id := 2
      groupPath := ["Claim", "Notes"]
      name := "Text"
      policy := { kind := .string }
      stringPolicy := { maxLength := some 2 }
      repeatableScope := [10] }
    let group : RepeatableGroupDecl := {
      level := 10
      path := ["Claim", "Notes"] }
    let model : FlatModel := {
      fields := [declaration]
      repeatableGroups := [group] }
    let raw : RawSingleGroupContext := {
      candidates := [1]
      read := fun _ _ => .parsed (.str "ABC") }
    (model.checkSingleGroupContext group raw).read 1 2 = {
      rawPresent := true
      parsed := none
      findings := [.declaredConstraint] } := by
  native_decide

/- Model checking owns the raw-mode and intrinsic String-policy laws. -/
example : errorOf ({ fields := [{ (stringDeclaration) with
      stringValueMode := .raw }] } : FlatModel).validate =
    some (.rawStringRequiresLineBreakPermission ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [{ (stringDeclaration {
      lineBreaksPermitted := true
      minLength := some 2 }) with stringValueMode := .raw }] } : FlatModel).validate =
    some (.rawStringForbidsMinimumLength ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [stringDeclaration {
      lineBreaksPermitted := true
      maxLength := some 1 }] } : FlatModel).validate =
    some (.lineBreakWithSingleCharacterMaximum ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [stringDeclaration {
      minLength := some 6
      maxLength := some 5 }] } : FlatModel).validate =
    some (.stringMinimumExceedsMaximum ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [{ (stringDeclaration {
      maxLength := some 5 }) with policy := { kind := .boolean } }] } :
      FlatModel).validate =
    some (.stringPolicyRequiresString ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [{ (stringDeclaration) with
      policy := { kind := .boolean }
      stringPatternSource := some "[0-9]+" }] } : FlatModel).validate =
    some (.stringPatternRequiresString ["Claim", "Note"]) := by
  native_decide

example : errorOf ({ fields := [{ (stringDeclaration {
      maxLength := some 5 }) with customType := some { name := "Code" } }] } :
      FlatModel).validate =
    some (.stringPolicyForbidsCustomType ["Claim", "Note"]) := by
  native_decide

/- A legal raw declaration may retain max-length metadata, but runtime formal checking skips it. -/
example :
    let declaration := { (stringDeclaration {
      lineBreaksPermitted := true
      maxLength := some 3 }) with stringValueMode := .raw }
    ({ fields := [declaration] } : FlatModel).validate.isOk = true := by
  native_decide

example :
    let declaration := { (stringDeclaration {
      lineBreaksPermitted := true
      maxLength := some 3 }) with stringValueMode := .raw }
    declaration.checkRaw (.parsed (.str "TOO-LONG")) = {
        rawPresent := true
        parsed := some (.str "TOO-LONG")
        findings := [] } := by
  native_decide

end A12Kernel.Conformance.StringFieldPolicy
