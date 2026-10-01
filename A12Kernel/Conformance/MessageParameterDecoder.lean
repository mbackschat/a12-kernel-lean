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

private def str (id : Nat) (group : List String) (name : String) (scope : List Nat := []) :
    FlatFieldDecl :=
  { id, groupPath := group, name, policy := { kind := .string }, repeatableScope := scope }

private def num (id : Nat) (group : List String) (name : String) (scope : List Nat := []) :
    FlatFieldDecl :=
  { id, groupPath := group, name, policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := scope }

/-- The retained flat model, whose second `Grade` under the repeatable `Cases2` makes that short name
ambiguous outside `Cases`. -/
private def model : FlatModel := {
  fieldRefByShortNameAllowed := true
  fields := [
    str 0 ["Probe"] "Anchor", str 1 ["Probe"] "Alpha", str 2 ["Probe"] "Beta",
    num 3 ["Probe"] "Amount", num 4 ["Probe"] "Total",
    str 5 ["Probe", "Claims"] "ClaimNo" [1], str 6 ["Probe", "Claims"] "Note" [1],
    num 7 ["Probe", "Claims"] "Payout" [1],
    num 8 ["Probe", "Cases"] "Score",
    { id := 9, groupPath := ["Probe", "Cases"], name := "Grade", policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["A", "B"], categories := [{ name := "Band", tokens := ["Hi", "Lo"] }] } },
    str 10 ["Probe", "Notes"] "Head" [2], str 11 ["Probe", "Notes"] "Tail" [2],
    str 12 ["Probe", "Outer"] "Key" [3], num 13 ["Probe", "Outer"] "OuterVal" [3],
    str 14 ["Probe", "Outer", "Inner"] "Key" [3, 4], str 15 ["Probe", "Outer", "Inner"] "Other" [3, 4],
    num 16 ["Probe", "Outer", "Inner"] "InnerVal" [3, 4],
    { id := 17, groupPath := ["Probe", "Cases2"], name := "Grade", policy := { kind := .enumeration },
      repeatableScope := [5],
      enumeration := some { storedTokens := ["X", "Y"], categories := [{ name := "Band", tokens := ["Hi", "Lo"] }] } },
    num 18 ["Probe", "Cases2"] "Score2" [5]]
  repeatableGroups := [
    { level := 1, path := ["Probe", "Claims"], repeatability := some 10, indexField := some 5 },
    { level := 2, path := ["Probe", "Notes"], repeatability := some 10, indexField := some 10 },
    { level := 3, path := ["Probe", "Outer"], repeatability := some 10, indexField := some 12 },
    { level := 4, path := ["Probe", "Outer", "Inner"], repeatability := some 10, indexField := some 14 },
    { level := 5, path := ["Probe", "Cases2"], repeatability := some 10, indexField := some 17 }] }

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

/- A spec opening on a name or a separator is read whole before any of its names is looked up, in a
key as in the name position, while one opening on a parent walk looks each name up as the parser
consumes it, in a key and in the group position alike. A turning point is compared by its first word,
and a category name is one token, so a dot after it is refused without reading on. A group-position
key's names are looked up on the group position's classes before its nesting and its gate
([settling batch](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
example :
    [
    ("Check $Score For Nope/$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $Score For Nope//x$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Score For Nope/%$.", ["MVK_LEXER_STANDARD_ERROR"]),
    ("Check $Score For /Nope/$.", ["MVK_INCOMPLETE_INPUT"]),
    ("Check $Score For Nope$.", ["INVALID_ENTITY"]),
    ("Check $Score For ../Nope/$.", ["INVALID_ENTITY"]),
    ("Check $#../Nope/$.", ["INVALID_GROUP"]),
    ("Check $#../Nope//x$.", ["INVALID_GROUP"]),
    ("Check $#../Nope/%$.", ["INVALID_GROUP"]),
    ("Check $#../Nope$.", ["INVALID_GROUP"]),
    ("Check $..Probe.x$.", ["INVALID_FIELD"]),
    ("Check $..Probe.x/Anchor$.", ["INVALID_FIELD"]),
    ("Check $Score For ..Probe.x$.", ["MVK_INDEX_FOR_ERROR_TEXT_INVALID"]),
    ("Check $#..Probe.x$.", []),
    ("Check $Grade->Nope.%$.", ["INVALID_CATEGORY"]),
    ("Check $Grade->Band.%$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $Grade->Band. %$.", ["MVK_UNEXPECTED_TOKEN"]),
    ("Check $#/Probe/Cases For Nope For \"k\"$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For Score For Nope$.", ["INVALID_GROUP"]),
    ("Check $#/Probe/Cases For /Nope$.", ["INVALID_ROOT_GROUP"]),
    ("Check $#/Probe/Cases For /Nope For \"k\"$.", ["INVALID_ROOT_GROUP"]),
    ("Check $#/Probe/Cases For ../../..$.", ["ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS"]),
    ("Check $#/Probe/Cases For ..Wrong$.", ["INVALID_ENTITY"]),
    ("Check $#/Probe/Cases For RuleGroup$.", ["none:ruleGroupUnresolved"]),
    ("Check $#/Probe/Cases For Nope$.", ["INVALID_GROUP"]),
    ("Check $Nope->Band x$.", ["INVALID_ENTITY"]),
    ("Check $Nope->Band$.", ["INVALID_ENTITY"])
    ].all (fun (template, kernel) => classes template == kernel) := by
  native_decide

end A12Kernel.Conformance.MessageParameterDecoder
