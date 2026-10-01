import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Conformance.ValidationMessageAuthoring

/-! # The message parameter decoder's acceptance matrix

Every expected list is the retained Kernel verdict of one rule-message row, run on the
probe grid's flat model and its repeatable twin with identical results, from a rule in `/Probe/Cases`
whose condition reads `Score` and `Grade`
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). A list
holds one class per refused parameter in written order, and an empty list is an admitted template.
`none:` names a refusal this fragment projects to no class: the one row, `$Score For RuleGroup$`, on
which the Kernel fails internally. -/

namespace A12Kernel.Conformance.MessageParameterDecoder

open A12Kernel
open A12Kernel.Conformance.ValidationMessageAuthoring (keywordProfile)

private def model : FlatModel := {
  fieldRefByShortNameAllowed := true
  fields := [
    { id := 0, groupPath := ["Probe", "Cases"], name := "Score", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 1, groupPath := ["Probe", "Cases"], name := "Grade", policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["A", "B"], categories := [{ name := "Band", tokens := ["A", "B"] }] } },
    { id := 2, groupPath := ["Probe"], name := "Anchor", policy := { kind := .string } }] }

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def arm (error : ValidationMessageTemplateError) : String :=
  ((reprStr error).takeWhile (!·.isWhitespace)).replace "A12Kernel.ValidationMessageTemplateError." ""

/-- The classes a template's refusals draw, one per refused parameter. -/
private def classes (template : String) : List String :=
  match elaborate model ["Probe", "Cases"] (.and (.fieldFilled (bare "Score")) (.fieldFilled (bare "Grade"))) with
  | .error _ => ["condition refused"]
  | .ok condition =>
      (validationMessageTemplateRefusals model keywordProfile condition template).map fun error =>
        (error.namedRuleDiagnostic?.map (·.kernelCode)).getD ("none:" ++ arm error)

/- Whitespace the lexer hides, anywhere in a parameter, and a category name that is one token: a token after it is refused only once the category's own gates pass, and an empty name draws its class before the kind gate. -/
example :
    [
    ("Check $Grade->Band$.", []),
    ("Check $Grade -> Band$.", []),
    ("Check $Grade-> Band$.", []),
    ("Check $Grade->Band $.", []),
    ("Check $Grade ->Band$.", []),
    ("Check $ Grade->Band$.", []),
    ("Check $Grade-> $.", ["NO_CATEGORY"]),
    ("Check $Grade->$.", ["NO_CATEGORY"]),
    ("Check $Score-> $.", ["NO_CATEGORY"]),
    ("Check $Grade->Band x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Grade->Band.value$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Grade->Band/Foo$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Grade->Nope x$.", ["INVALID_CATEGORY"]),
    ("Check $Score->Band x$.", ["FIELD_NO_ENUM"]),
    ("Check $ Score$.", []),
    ("Check $Score $.", []),
    ("Check $Score .value$.", []),
    ("Check $Score. value$.", []),
    ("Check $Score$.", [])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

/- A key, spaced or not, and a literal that contains the key terminal, reach the index gate, which refuses every key on a condition that reads none; a keyed key draws the nesting class first, and the rule-group terminal as a field draws its own class after its key's nesting. As a key it fails inside the Kernel, a defect this fragment leaves unclassed. -/
example :
    [
    ("Check $Score For  \"k\"$.", ["MVK_INDEX_FOR_ERROR_TEXT_INVALID"]),
    ("Check $Score For\"k\"$.", ["MVK_INDEX_FOR_ERROR_TEXT_INVALID"]),
    ("Check $Score  For \"k\"$.", ["MVK_INDEX_FOR_ERROR_TEXT_INVALID"]),
    ("Check $Score For \"a For b\"$.", ["MVK_INDEX_FOR_ERROR_TEXT_INVALID"]),
    ("Check $Score For Grade For \"a For b\"$.", ["ILLEGAL_SEMANTIC_INDEX"]),
    ("Check $RuleGroup For Score For \"k\"$.", ["ILLEGAL_SEMANTIC_INDEX"]),
    ("Check $Score For RuleGroup$.", ["none:ruleGroupUnresolved"]),
    ("Check $Nope For Score.x$.", ["INVALID_ENTITY"]),
    ("Check $Nope For \"k\" x$.", ["INVALID_ENTITY"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

/- The group position's key: the group's own lookup answers first, then the key's nesting or syntax, then the key's gate, `INVALID_GROUP` on an admitted group too; a group keyword followed by a key reads as a name, and the rule-group shorthand keeps its keyword. -/
example :
    [
    ("Check $#Cases For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#Cases For Score$.", ["INVALID_GROUP"]),
    ("Check $#Cases For Score For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#Cases For Nope$.", ["INVALID_GROUP"]),
    ("Check $#Cases$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases$.", []),
    ("Check $#/Probe/Cases For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For Score$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For Score For \"k\"$.", ["ILLEGAL_SEMANTIC_INDEX"]),
    ("Check $#/Probe/Cases For Nope$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For Grade$.", ["INVALID_GROUP"]),
    ("Check $#/Probe For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#RootGroup For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#RuleGroup For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#Zeile For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#RuleGroup For$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $#/Probe/Cases For \"k\" x$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For Score/$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $#/Probe/Cases For Nope/x$.", ["INVALID_GROUP"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

/- Each parameter is checked on its own and reports its own first failure. -/
example :
    [
    ("Check $Nope$ and $Score$.", ["INVALID_ENTITY"]),
    ("Check $Nope$ and $Gradé$.", ["INVALID_ENTITY", "MVK_LEXER_STANDARD_ERROR"]),
    ("Check $Nope$ and $Nope2$.", ["INVALID_ENTITY", "INVALID_ENTITY"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

/- The name position's decision reads the whole entity spec and the token after it before any check, so a fault there answers before the name's lookup; past that window the key's syntax answers before the field's check, and the field's or Base Year's check before a token left at the end. -/
example :
    [
    ("Check $Nope x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Nope/$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $Nope//Score$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Score x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Score/$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $Nope.Vordruckzeile x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Nope.value x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Nope For$.", ["INVALID_ENTITY"]),
    ("Check $Score For$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $Grade->Nope For$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $BaseYear x$.", ["NO_BASE_YEAR"]),
    ("Check $BaseYear+$.", ["MVK_EXPECTED_TOKEN_NOT_FOUND"]),
    ("Check $RuleGroup$.", ["INVALID_PARAMETER"]),
    ("Check $RuleGroup->Band$.", ["INVALID_PARAMETER"]),
    ("Check $RuleGroup x$.", ["MVK_UNEXPECTED_TOKEN"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

/- A bare parent walk names the group it reaches, and a lexer fault answers where its token is fetched. -/
example :
    [
    ("Check $..$.", ["INVALID_FIELD"]),
    ("Check $..Probe$.", ["INVALID_FIELD"]),
    ("Check $..Nope$.", ["INVALID_ENTITY"]),
    ("Check $../..$.", ["ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS"]),
    ("Check $Nope For é$.", ["INVALID_ENTITY"]),
    ("Check $Grade->Nope é$.", ["MVK_LEXER_STANDARD_ERROR"]),
    ("Check $Nope é$.", ["MVK_LEXER_STANDARD_ERROR"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

end A12Kernel.Conformance.MessageParameterDecoder
