import A12Kernel.Conformance.ValidationMessageAuthoring

/-! # Message group position conformance locks

The group position `$#…$` checked inside a whole rule-message template: which groups are available
to the rule's message, how a decoded argument resolves against the rule's group, which class each
refused spelling draws once the model is consulted, and what an admitted group renders, on spellings
translated to the shared fixture's `Order`, `Head`, `Deeper`, `Base`, `Side` and `Vendor` groups. A
case cites its checkpoint where one settles it; an uncited case locks this module's account of the
group position, whose Kernel 30.8.1 measurements the group-position checkpoints in
`docs/sources/message-and-pointer-probes.md` own. The decoder's model-free decisions are locked in
`Conformance/MessageGroupArgument.lean`.
-/

namespace A12Kernel.Conformance.MessageGroupPosition

open A12Kernel
open A12Kernel.Conformance.ValidationMessageAuthoring

/-- A rule in `/Order/Head`, whose group has one ancestor above it, one **declared** group below it,
and one declared sibling. Every group-position case below runs against this one rule. -/
private def headGroupOk? (template : String) : Option Bool :=
  pathTemplateOk? ["Order", "Head"] (bare "Amount") template

private def headGroupError? (template : String) :
    Option ValidationMessageTemplateError :=
  pathTemplateError? ["Order", "Head"] (bare "Amount") template

/- The **group position** `$#...$`. Measured at kernel 30.8.1, the rule's own group and its ancestors
are always available, which is the arm these rows exercise; a group the condition reads into is the
other arm, locked below. The two keyword shorthands name the endpoints of the ancestor chain and are
admitted here for that reason, not as separate admissions — but **`RuleGroup`
additionally carries a placement condition**, so that shared reason is not the whole rule: a rule
sitting directly in the root group may not write `$#RuleGroup$` at all, while `$#RootGroup$` and the
absolute spelling of that very group are both admitted from the same locus. The rows here are one
level down, where all four spellings are admitted; the root-locus rows below are where the shorthand
parts from the other two. Measured on the computation carrier first
([checkpoint](../../docs/SOURCES.md#src-rulegroup-shorthand-root-gate)) and then on this one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)),
which is the crossing that closed it. -/
example :
    headGroupOk? "In $#/Order/Head$" = some true ∧
      headGroupOk? "In $#/Order$" = some true ∧
      headGroupOk? "In $#RuleGroup$" = some true ∧
      headGroupOk? "In $#RootGroup$" = some true := by
  native_decide

/- The refused half, and the separator that makes availability the operative gate rather than mere
existence: `/Order/Head/Deeper` and `/Order/Side` are groups this model really **declares**, and both
are refused exactly like the unknown `/Order/Nope`, because this condition reads nothing inside either.
The same two groups are admitted once the condition reads into them, below. -/
example :
    headGroupError? "In $#/Order/Head/Deeper$" =
        some (.invalidGroupParameter "#/Order/Head/Deeper") ∧
      headGroupError? "In $#/Order/Side$" =
        some (.invalidGroupParameter "#/Order/Side") ∧
      headGroupError? "In $#/Order/Nope$" =
        some (.invalidGroupParameter "#/Order/Nope") := by
  native_decide

/- A path without the leading separator is **relative to the rule's group**, so a bare word names a
group *below* it. `Head` is the rule's own group and `Order` its ancestor, both admitted when spelled
absolutely above, but spelled bare they name `/Order/Head/Head` and `/Order/Head/Order`, which do not
exist; a bare word is not looked up as the short name of a group elsewhere. A field name in this
position is refused like any other word
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). -/
example :
    headGroupError? "In $#Head$" = some (.invalidGroupParameter "#Head") ∧
      headGroupError? "In $#Order$" = some (.invalidGroupParameter "#Order") ∧
      headGroupError? "In $#Amount$" = some (.invalidGroupParameter "#Amount") := by
  native_decide

/- A group the condition **reads into** is available whatever its position relative to the rule: the
root-group rule reading `Head/Deeper/Deep` admits the descendant `Deeper`, and the intermediate `Head`
that holds no read field directly, in the relative and the absolute spelling alike. The same rule still
refuses the unread sibling, an unknown relative group, and a relative path naming the read field
itself; and a bare `Deeper`, which is available by path, is refused because nothing named so sits
directly below the rule's group
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). -/
example :
    let deep := pathAt (.relative 0) ["Head", "Deeper"] "Deep"
    pathTemplateOk? ["Order"] deep "In $#Head$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#Head/Deeper$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#/Order/Head/Deeper$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#'Head'$" = some true ∧
      pathTemplateError? ["Order"] deep "In $#Deeper$" =
        some (.invalidGroupParameter "#Deeper") ∧
      pathTemplateError? ["Order"] deep "In $#Side$" =
        some (.invalidGroupParameter "#Side") ∧
      pathTemplateError? ["Order"] deep "In $#Head/Nope$" =
        some (.invalidGroupParameter "#Head/Nope") ∧
      pathTemplateError? ["Order"] deep "In $#Head/Deeper/Deep$" =
        some (.invalidGroupParameter "#Head/Deeper/Deep") := by
  native_decide

/- A **read sibling** is available too, so availability is not containment in either direction. From
`/Order/Head` reading `/Order/Side/Aside`, the sibling is admitted by a parent walk, by an absolute
path, and by a walk whose turning point names the group it reaches; a turning point naming another
group is refused on the Kernel's entity class, not the group one. -/
example :
    let aside := pathAt .absolute ["Order", "Side"] "Aside"
    pathTemplateOk? ["Order", "Head"] aside "In $#../Side$" = some true ∧
      pathTemplateOk? ["Order", "Head"] aside "In $#/Order/Side$" = some true ∧
      pathTemplateOk? ["Order", "Head"] aside "In $#..Order/Side$" = some true ∧
      pathTemplateError? ["Order", "Head"] aside "In $#..Wrong/Side$" =
        some (.turningPointMismatch "#..Wrong/Side") := by
  native_decide

/- A parent walk reaches the ancestor arm, and one that climbs past the root group is refused on the
message route's own above-root class. A bare `..` names the parent itself. -/
example :
    headGroupOk? "In $#..$" = some true ∧
      headGroupOk? "In $#../Head$" = some true ∧
      headGroupError? "In $#../Side$" = some (.invalidGroupParameter "#../Side") ∧
      headGroupError? "In $#Deeper$" = some (.invalidGroupParameter "#Deeper") ∧
      headGroupError? "In $#../../Order$" =
        some (.parameterAboveRoot "#../../Order") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#../Head$" =
        some (.parameterAboveRoot "#../Head") := by
  native_decide

/- The argument is refused in **layers**
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)). Its
decoder's lexer and syntax classes, locked in `Conformance/MessageGroupArgument.lean`, answer before
the lookup even on an unknown name, which the first two rows witness through the whole template;
then the path is looked up, and only a path that resolves meets the syntax class for a token left
after it. -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    deep "In $#Nope[1]$" = some (.parameterSyntax "#Nope[1]" .lexer) ∧
      deep "In $#Nope/$" = some (.parameterSyntax "#Nope/" .truncated) ∧
      deep "In $#He-ad$" = some (.invalidGroupParameter "#He-ad") ∧
      deep "In $#/Order/He-ad$" = some (.invalidGroupParameter "#/Order/He-ad") ∧
      deep "In $#Head-x$" = some (.parameterSyntax "#Head-x" .unexpected) ∧
      deep "In $#Head)$" = some (.parameterSyntax "#Head)" .unexpected) ∧
      deep "In $#Head x$" = some (.parameterSyntax "#Head x" .unexpected) ∧
      deep "In $#/Order/Head-x$" =
        some (.parameterSyntax "#/Order/Head-x" .unexpected) ∧
      headGroupError? "In $#...$" = some (.parameterSyntax "#..." .unexpected) := by
  native_decide

/- A bare word that names nothing directly below the rule's group is looked up as the **short name of
a field**, never of a group. `Amount` is declared twice, so from `/Order/Side` it is ambiguous and
refused on its own class; the unique field `Aside`, reached that way from the root group, is refused
as a field. A group whose name is unique is not found this way at all, which is what refuses a bare
`Deeper` from the root group above. -/
example :
    pathTemplateError? ["Order", "Side"] (bare "Aside") "In $#Amount$" =
        some (.groupShortNameNotUnique "#Amount" "Amount") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#Aside$" =
        some (.invalidGroupParameter "#Aside") := by
  native_decide

/- The descendant arm from a rule below the root, and a parent walk that reaches the root group
exactly, beside one step more. -/
example :
    pathTemplateOk? ["Order", "Head"] (pathAt (.relative 0) ["Deeper"] "Deep") "In $#Deeper$" =
        some true ∧
      pathTemplateOk? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../..$" = some true ∧
      pathTemplateError? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../../..$" =
        some (.parameterAboveRoot "#../../..") := by
  native_decide

/- Two historic terminals are **recognized** in this position and refused on their own class, which the
Kernel reports with a code distinct from an unknown group. Other words that look like terminals of
the same vintage are not terminals here at all: they draw the ordinary unknown-group refusal, and so
does an arbitrary name, so the retired class is exactly two members wide rather than a catch-all for
old syntax. The Kernel's `$#index(Rows)$` row, measured on a model with no field of that name, is not
locked here, because this fixture declares a field `index` that the bare word's short-name lookup
would find. -/
example :
    headGroupError? "In $#Zeile$" = some (.retiredGroupTerminal "#Zeile" "Zeile") ∧
      headGroupError? "In $#Usb$" = some (.retiredGroupTerminal "#Usb" "Usb") ∧
      headGroupError? "In $#Vordruckzeile$" =
        some (.invalidGroupParameter "#Vordruckzeile") ∧
      headGroupError? "In $#Vordruckname$" =
        some (.invalidGroupParameter "#Vordruckname") ∧
      headGroupError? "In $#NotATerminal$" =
        some (.invalidGroupParameter "#NotATerminal") := by
  native_decide

/- The position marker selects a **different grammar**, not a different form inside the name grammar:
the same word is an entity lookup without it and a group terminal with it. That is the pair the Kernel
separates by reporting an entity refusal for one spelling and admitting the other. -/
example :
    headGroupOk? "In $#RootGroup$" = some true ∧
      headGroupError? "In $RootGroup$" =
        some (.reference "RootGroup"
          (.invalidEntity (pathAt (.relative 0) [] "RootGroup"))) := by
  native_decide

/- At the root the chain has one member, so the three spellings would all denote that one group — and
the Kernel refuses exactly one of them. A rule sitting directly in the root group may not write the
`RuleGroup` shorthand, while `RootGroup` and the absolute spelling of that very group are admitted
from the identical locus
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)).
So the gate is on the word, not on the position: the group is nameable there twice over. The group
below — admitted as the *rule's own* group one row above — is still refused here, because this
condition reads nothing inside it. -/
example :
    pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup$" =
        some (.ruleGroupImmediatelyBelowRoot "#RuleGroup") ∧
      pathTemplateOk? ["Order"] (bare "Other") "In $#RootGroup$" = some true ∧
      pathTemplateOk? ["Order"] (bare "Other") "In $#/Order$" = some true ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#/Order/Head$" =
        some (.invalidGroupParameter "#/Order/Head") := by
  native_decide

/- One level down the same shorthand is admitted, which is what makes the row above a placement gate
   rather than the shorthand being unsupported. -/
example :
    pathTemplateOk? ["Order", "Head"] (bare "Amount") "In $#RuleGroup$" =
      some true := by
  native_decide

/- `RuleGroup`, and `RootGroup` followed by any token but a separator, stay the keyword, so the
keyword's own gate answers before the token left after it, exactly as a resolving path's lookup does.
From the root group `RuleGroup` draws its
placement refusal with a separator or a `-` after it; one level down it resolves, and the token left
after it draws the syntax class. `RootGroup` with a `-` after it resolves the same way, but with a
separator after it the argument is a path whose first segment names no group below the rule's group
(a12-dmkits `MessageGroupArgumentAgreementTest` at `c785a4b6f`, Kernel 30.8.1,
[inbound](../../docs/SOURCES.md#inbound-2026-10-01-group-arguments)). -/
example :
    let aside := pathAt .absolute ["Order", "Side"] "Aside"
    let deep := pathAt (.relative 0) ["Head", "Deeper"] "Deep"
    pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup/Head$" =
        some (.ruleGroupImmediatelyBelowRoot "#RuleGroup/Head") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup-x$" =
        some (.ruleGroupImmediatelyBelowRoot "#RuleGroup-x") ∧
      pathTemplateError? ["Order", "Head"] aside "In $#RuleGroup/Deeper$" =
        some (.parameterSyntax "#RuleGroup/Deeper" .unexpected) ∧
      pathTemplateError? ["Order", "Head"] aside "In $#RuleGroup-x$" =
        some (.parameterSyntax "#RuleGroup-x" .unexpected) ∧
      pathTemplateError? ["Order"] deep "In $#RootGroup/Head$" =
        some (.invalidGroupParameter "#RootGroup/Head") ∧
      pathTemplateError? ["Order"] deep "In $#RootGroup-x$" =
        some (.parameterSyntax "#RootGroup-x" .unexpected) := by
  native_decide

/- The decoder's event order, locked in `Conformance/MessageGroupArgument.lean`, meets the lookup and
availability here ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)).
A retired offset alternative draws its class through the whole template. A keyword-and-name word before
a separator, and a run of digits, are path segments the lookup refuses. A lexer fault right after a
complete alternative answers before its availability and before the root-placement gate, while a path
that resolves to an unavailable group draws the group class before the token left after it. -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    deep "In $#Zeile-1$" = some (.retiredGroupTerminal "#Zeile-1" "Zeile") ∧
      deep "In $#Zeile/Head$" = some (.invalidGroupParameter "#Zeile/Head") ∧
      deep "In $#Usb/Head$" = some (.invalidGroupParameter "#Usb/Head") ∧
      deep "In $#123$" = some (.invalidGroupParameter "#123") ∧
      deep "In $#Head/123$" = some (.invalidGroupParameter "#Head/123") ∧
      deep "In $#RootGroup+1$" = some (.parameterSyntax "#RootGroup+1" .unexpected) ∧
      deep "In $#Side%$" = some (.parameterSyntax "#Side%" .lexer) ∧
      deep "In $#Side-x$" = some (.invalidGroupParameter "#Side-x") ∧
      deep "In $#/Order/Side-x$" = some (.invalidGroupParameter "#/Order/Side-x") ∧
      deep "In $#Side)$" = some (.invalidGroupParameter "#Side)") ∧
      deep "In $#Side x%$" = some (.invalidGroupParameter "#Side x%") ∧
      deep "In $#Head x%$" = some (.parameterSyntax "#Head x%" .unexpected) ∧
      deep "In $#'Zeile'-1$" = some (.invalidGroupParameter "#'Zeile'-1") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup+1$" =
        some (.ruleGroupImmediatelyBelowRoot "#RuleGroup+1") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup%$" =
        some (.parameterSyntax "#RuleGroup%" .lexer) := by
  native_decide

/-- A model whose root holds a group literally named `RootGroup`, so a path through it can resolve. -/
private def keywordGroupModel : FlatModel :=
  { fields := [other,
      { id := 2, groupPath := ["Order", "RootGroup", "Inner"], name := "W",
        policy := { kind := .string } }] }

private def keywordGroupOk? (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option Bool := do
  let condition ← (elaborate keywordGroupModel group (.fieldFilled reference)).toOption
  pure (elaborateValidationMessageTemplate keywordGroupModel keywordProfile condition
    template).toOption.isSome

/- Followed by a separator, `RootGroup` is the first segment of a path that resolves to the group of
that name, while alone it still names the root; quoted, it is that group too. -/
example :
    let w := pathAt (.relative 0) ["RootGroup", "Inner"] "W"
    keywordGroupOk? ["Order"] w "In $#RootGroup/Inner$" = some true ∧
      keywordGroupOk? ["Order"] w "In $#RootGroup$" = some true ∧
      keywordGroupOk? ["Order"] w "In $#'RootGroup'$" = some true ∧
      keywordGroupOk? ["Order"] w "In $#'RootGroup'/Inner$" = some true ∧
      keywordGroupOk? ["Order"] w "In $#/Order/RootGroup/Inner$" = some true ∧
      keywordGroupOk? ["Order", "RootGroup", "Inner"] (bare "W") "In $#..RootGroup$" =
        some true := by
  native_decide

/- With the group named `RootGroup` unread, the readings part: the bare word still names the root and is
admitted, while the quoted word and the path through it name that unavailable group. -/
example :
    keywordGroupOk? ["Order"] (bare "Other") "In $#RootGroup$" = some true ∧
      keywordGroupOk? ["Order"] (bare "Other") "In $#'RootGroup'$" = some false ∧
      keywordGroupOk? ["Order"] (bare "Other") "In $#RootGroup/Inner$" = some false := by
  native_decide

/- A reserved word outside the quoting-exempt set refuses a segment through the whole template, an
exempt word is a name the lookup refuses, and after a parent walk `RuleGroup` is a token left after
the resolved parent while `RootGroup` is a turning point naming another group. -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    deep "In $#Head/RuleGroup$" = some (.parameterSyntax "#Head/RuleGroup" .unexpected) ∧
      deep "In $#Head/value$" = some (.invalidGroupParameter "#Head/value") ∧
      deep "In $#index/Head$" = some (.invalidGroupParameter "#index/Head") ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#..RuleGroup$" =
        some (.parameterSyntax "#..RuleGroup" .unexpected) ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#..RootGroup$" =
        some (.turningPointMismatch "#..RootGroup") := by
  native_decide

/- The parent walk's check is an action at the end of the walk, so it answers before any fault in the
names after it, and before a turning point's dotted continuation, which only its first word is
compared by. Two or more up-steps ending on a separator before a token that continues no name count
one step more, which only a walk reaching the root exactly can show
([inbound](../../docs/SOURCES.md#inbound-2026-10-01a-parent-walk-and-dotted-names), [checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)). -/
example :
    let base := pathTemplateError? ["Order", "Head", "Deeper", "Base"] (bare "Bottom")
    let deeper := pathTemplateError? ["Order", "Head", "Deeper"] (bare "Deep")
    pathTemplateError? ["Order"] (bare "Other") "In $#../RuleGroup$" =
        some (.parameterAboveRoot "#../RuleGroup") ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#..Wrong/$" =
        some (.turningPointMismatch "#..Wrong/") ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#..Wrong/%$" =
        some (.turningPointMismatch "#..Wrong/%") ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#../../Head//%$" =
        some (.parameterAboveRoot "#../../Head//%") ∧
      deeper "In $#../../RuleGroup$" = some (.parameterAboveRoot "#../../RuleGroup") ∧
      deeper "In $#../../$" = some (.parameterAboveRoot "#../../") ∧
      deeper "In $#../..//$" = some (.parameterAboveRoot "#../..//") ∧
      deeper "In $#../../%$" = some (.parameterSyntax "#../../%" .lexer) ∧
      deeper "In $#../../Nope$" = some (.invalidGroupParameter "#../../Nope") ∧
      base "In $#../../$" = some (.parameterSyntax "#../../" .expectedToken) ∧
      base "In $#../../RuleGroup$" =
        some (.parameterSyntax "#../../RuleGroup" .unexpected) ∧
      base "In $#../..//$" = some (.parameterSyntax "#../..//" .unexpected) ∧
      base "In $#../../../RuleGroup$" =
        some (.parameterAboveRoot "#../../../RuleGroup") ∧
      pathTemplateError? ["Order", "Head"] (bare "Amount") "In $#../$" =
        some (.parameterSyntax "#../" .truncated) ∧
      pathTemplateOk? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../../Head$" = some true ∧
      pathTemplateOk? ["Order", "Head"] (bare "Amount") "In $#..Order.x$" = some true := by
  native_decide

/- A dotted continuation is part of its name segment, so the segment names no group, while a word that
cannot continue it is a token left after the path. An exempt word may continue one and, except the
value suffix and the form-pointer terminals, end it; a keyword-and-name word continued by a dot is a
path segment. -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    deep "In $#Head.Deeper$" = some (.invalidGroupParameter "#Head.Deeper") ∧
      deep "In $#Head.'Deeper'$" = some (.invalidGroupParameter "#Head.'Deeper'") ∧
      deep "In $#Head.x/Deeper$" = some (.invalidGroupParameter "#Head.x/Deeper") ∧
      deep "In $#Head.x.y$" = some (.invalidGroupParameter "#Head.x.y") ∧
      deep "In $#Head.Zeile$" = some (.invalidGroupParameter "#Head.Zeile") ∧
      deep "In $#Head.value.x$" = some (.invalidGroupParameter "#Head.value.x") ∧
      deep "In $#RootGroup.x$" = some (.invalidGroupParameter "#RootGroup.x") ∧
      deep "In $#Zeile.x$" = some (.invalidGroupParameter "#Zeile.x") ∧
      deep "In $#'RootGroup'.x$" = some (.invalidGroupParameter "#'RootGroup'.x") ∧
      (["Head.value", "Head.Vordruckname", "Head.RuleGroup", "Head.For", "Head.1", "Head."].all
        fun argument => deep s!"In $#{argument}$" =
          some (.parameterSyntax s!"#{argument}" .unexpected)) = true ∧
      (["Head.'value'", "Head.'RuleGroup'", "Head.'For'"].all fun argument =>
        deep s!"In $#{argument}$" = some (.invalidGroupParameter s!"#{argument}")) = true := by
  native_decide

/- The cold review's rows, each measured: a retired offset's digits are no name, so a dot after them is
a token after the retired alternative; a lexer fault right after a dot answers before the check its
name waits for; a turning point's first word is still compared; any token after the last separator
that continues no name extends the run, while a run of digits or a quoted name ends it; and an exempt
word may stand inside a dotted name ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)). -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    let head := pathTemplateError? ["Order", "Head"] (bare "Amount")
    let deeper := pathTemplateError? ["Order", "Head", "Deeper"] (bare "Deep")
    pathTemplateError? ["Order"] (bare "Other") "In $#Zeile-1.x$" =
        some (.retiredGroupTerminal "#Zeile-1.x" "Zeile") ∧
      deep "In $#Head.%$" = some (.parameterSyntax "#Head.%" .lexer) ∧
      deep "In $#Head.'x$" = some (.parameterSyntax "#Head.'x" .lexer) ∧
      head "In $#..Wrong.%$" = some (.parameterSyntax "#..Wrong.%" .lexer) ∧
      head "In $#..Wrong.x$" = some (.turningPointMismatch "#..Wrong.x") ∧
      head "In $#..Wrong/..$" = some (.turningPointMismatch "#..Wrong/..") ∧
      deeper "In $#../../-x$" = some (.parameterAboveRoot "#../../-x") ∧
      deeper "In $#../../($" = some (.parameterAboveRoot "#../../(") ∧
      deeper "In $#../../123$" = some (.invalidGroupParameter "#../../123") ∧
      pathTemplateOk? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../../'Head'$" = some true ∧
      (["Head.Vordruckname.x", "Head.Usb.x", "Head.RootGroup.x"].all fun argument =>
        deep s!"In $#{argument}$" = some (.invalidGroupParameter s!"#{argument}")) = true := by
  native_decide

/- The peer's turning-point rows on this fixture: the turning point is checked before the child below
it ([inbound](../../docs/SOURCES.md#inbound-2026-10-01-group-arguments)). -/
example :
    let aside := pathAt .absolute ["Order", "Side"] "Aside"
    pathTemplateError? ["Order", "Head"] aside "In $#..Wrong/Missing$" =
        some (.turningPointMismatch "#..Wrong/Missing") ∧
      pathTemplateError? ["Order", "Head"] aside "In $#..Order/Missing$" =
        some (.invalidGroupParameter "#..Order/Missing") := by
  native_decide

/- The group argument takes the name grammar's **single-quote escape** at any segment, and the quotes
are erased before the group is looked up, so a quoted spelling reaches the same group as its bare one. -/
example :
    headGroupOk? "In $#/'Order'/'Head'$" = some true ∧
      headGroupOk? "In $#/'Order'/Head$" = some true ∧
      headGroupOk? "In $#/Order/'Head'$" = some true ∧
      headGroupOk? "In $#/'Order'$" = some true := by
  native_decide

/- Quoting is not merely erased, though: it **suppresses** the keyword reading. Each of these three
words is a terminal in this position unquoted — two admitted, one on the retired class — and quoting
all three turns them into ordinary group names, which are then refused because no group of that name
sits below the rule's group. That is the separator between "quotes are stripped first" and "quotes decide whether the
word is a terminal at all". -/
example :
    headGroupError? "In $#'RootGroup'$" =
        some (.invalidGroupParameter "#'RootGroup'") ∧
      headGroupError? "In $#'RuleGroup'$" =
        some (.invalidGroupParameter "#'RuleGroup'") ∧
      headGroupError? "In $#'Zeile'$" = some (.invalidGroupParameter "#'Zeile'") := by
  native_decide

/- An absolute path resolves in **two stages**, and the Kernel reports them apart. The first segment
must name a declared root group; when it does not, the refusal is the root one whatever follows it. A
declared root followed by an unknown or unavailable group is the ordinary group refusal instead, so
root existence and availability are separate gates rather than one. -/
example :
    headGroupError? "In $#/Nope$" = some (.unknownRootGroup "#/Nope" "Nope") ∧
      headGroupError? "In $#/Nope/Head$" =
        some (.unknownRootGroup "#/Nope/Head" "Nope") ∧
      headGroupError? "In $#/Order/Nope$" =
        some (.invalidGroupParameter "#/Order/Nope") := by
  native_decide

/- The root shorthand names the root of the **rule's own** ancestor chain, not a model-wide root. A
second root group separates the two readings: a rule under it admits the shorthand while the other
root, which neither contains the rule nor holds a read field, is refused. -/
example :
    pathTemplateOk? ["Vendor", "Branch"] (bare "Label") "In $#RootGroup$" =
        some true ∧
      pathTemplateOk? ["Vendor", "Branch"] (bare "Label") "In $#/Vendor$" =
        some true ∧
      pathTemplateError? ["Vendor", "Branch"] (bare "Label") "In $#/Order$" =
        some (.invalidGroupParameter "#/Order") := by
  native_decide

/- What an admitted **group** parameter renders, measured on the Kernel: the 1-based repetition index
   of the named group in the firing row, and `1` for a nonrepeatable group. A three-row document
   whose rule fires on rows 2 and 3 renders `2` and `3`, which separates the row's own index from a
   firing ordinal
   ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index)).
   Only the nonrepeatable arm is reachable here, and deliberately so: an available group is an
   ancestor of the rule's row group or holds a field the condition reads, and this route's condition
   spine refuses a repeatable reference, so neither arm reaches a repeatable group. What these cases lock is that
   the bytes are the **Kernel's constant** rather than the caller's, which is what they used to be. -/

example : render? "[root=$#/Order$]" = some { text := "[root=1]" } := by
  native_decide

example : render? "[rtg=$#RootGroup$]" = some { text := "[rtg=1]" } := by
  native_decide

/-- The rule's own group is this model's root, so the shorthand never reaches rendering at all: the
    placement gate refuses it during authoring, and this row records that the render route is
    unreachable from this host rather than that it renders something. A rendered `RuleGroup` needs a
    rule one level down, which this fixture's nonrepeatable spine does not carry. -/
example : render? "[rg=$#RuleGroup$]" = none := by
  native_decide

/-- The Kernel code a group-position refusal projects to, for a rule in `group` reading `reference`. -/
private def groupClass? (group : GroupPath) (reference : SurfaceFieldPath) (template : String) :
    Option (Option String) :=
  (pathTemplateError? group reference template).map fun error =>
    error.namedRuleDiagnostic?.map KernelStaticDiagnostic.kernelCode

/- Every refusal the group position draws once the model is consulted projects to the Kernel's class:
an unknown or unavailable group, an ambiguous short name, a walk past the root, a wrong turning
point, an unknown root, a retired terminal and the rule-group shorthand at the root. -/
example :
    let deep := groupClass? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    let head := groupClass? ["Order", "Head"] (bare "Amount")
    deep "In $#Side$" = some (some "INVALID_GROUP") ∧
      groupClass? ["Order", "Side"] (bare "Aside") "In $#Amount$" =
        some (some "ERROR_TEXT_FIELDNAME_NOT_UNIQUE") ∧
      head "In $#../..$" = some (some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS") ∧
      head "In $#..Wrong$" = some (some "INVALID_ENTITY") ∧
      deep "In $#/Nope$" = some (some "INVALID_ROOT_GROUP") ∧
      deep "In $#Zeile$" = some (some "PARAM_INVALID_IN_NEW_WORLD") ∧
      deep "In $#RuleGroup$" = some (some "RULEGROUP_IMMEDIATELY_BELOW_ROOT") := by
  native_decide

end A12Kernel.Conformance.MessageGroupPosition
