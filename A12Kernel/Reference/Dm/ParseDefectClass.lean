import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.HavingAdmission

/-! # The first class a text with a parse defect raises

The Kernel resolves each entity reference as its parse takes it, so a condition or operation carrying
both a parse defect and an unresolvable name reports whichever comes first in the text: `FieldFilled(Nope)
And And FieldFilled(Value)` reports the name, `FieldFilled(Value) And And FieldFilled(Nope)` the token
(rows `r-two-defects-*` of the [declaration-report capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)).
This reader parses the whole text before lowering it, so it recovers that order from the references and walked path steps the
parser completed before it failed. A text that parses has its classes from lowering, not from here.
-/

namespace A12Kernel.Dm

/-- The resolution class of one written field path read from `group`, `none` when it names a declared
field or group. A path naming a group displaces only the misses a group-reading site displaces. -/
private def fieldPathClass? (model : FlatModel) (group : GroupPath) (field : SurfaceFieldPath) :
    Option KernelStaticDiagnostic :=
  match model.resolveFieldDeclarationUnchecked group field with
  | .ok _ => none
  | .error error =>
      if error.isGroupDisplaceableMiss && (model.groupNamedBy? group field).isSome then none
      else error.diagnostic?

/-- The resolution class of a closed reference's path, `none` for a path with a star, a correlation or
an index, whose gates belong to lowering. -/
def referenceResolutionClass? (model : FlatModel) (group : GroupPath) (path : Path) :
    Option KernelStaticDiagnostic :=
  path.toFieldPath?.bind (fieldPathClass? model group)

/-- The class a whole reference's ordered read raises, its reads bound at `bindingGroup`, `none` when
it admits: a starred path's resolution and an unbound repeatable level. A reference before a stray
name draws its `MVK_NO_WILDCARD` and a starred path naming nothing its `MVK_INVALID_ENTITY` (rows `A01`
and `A20` of the [parser-index batch](../../../evidence/kernel-30.8.1/captures/parser-index-and-iteration-classes/)). -/
def referenceReadClass? (model : FlatModel) (group bindingGroup : GroupPath) (reference : Reference) :
    Option KernelStaticDiagnostic :=
  match checkReferenceRead model group bindingGroup reference with
  | .ok _ => none
  | .error refusal => KernelStaticDiagnostic.all.find? (·.kernelCode == refusal.detail)

/-- The class of the first step of a path left open that names nothing. Only a walked path checks its
steps: one that is `$`-marked, opens with an up-run, or has read a starred step (spec/12 §12.3); a step
is judged by its name alone, its star aside. -/
def openPathClass? (model : FlatModel) (group : GroupPath) (path : Path) :
    Option KernelStaticDiagnostic :=
  if !(path.correlated || 0 < path.ups || path.segments.any (·.star)) then none else
  (List.range path.segments.length).findSome? fun index =>
    let steps := path.segments.take (index + 1)
    let step : SurfaceFieldPath := {
      base := path.base
      turningPoint := path.turningPoint
      groups := steps.dropLast.map (·.name)
      field := (steps.getLast?.map (·.name)).getD "" }
    fieldPathClass? model group step

/-- The class a text with a parse defect raises first: the class of the first completed event that
resolves to nothing or whose operation gate refuses, otherwise the defect's own class. `none` for a text
that parses. `MVK_INVALID_ENTITY` and `MVK_INVALID_ROOT_GROUP` and a date operation's `MVK_NO_DATE`
ahead of a token defect are measured (predicate-operand capture, 2026-10-14), and so is a whole
reference's `MVK_NO_WILDCARD` (parser-index rows); another class in that position is this account's
extension. A lexer defect is reported with no event before it, because the
lexer reads the whole text first; where the Kernel's lexer stops is unmeasured. A completed operation's
reads bind at `bindingGroup`, the error field's group, as an admitted rule's do: `AddDays(Items/ShipOn, 1)`
before a bare value slot reports no unbound star (handback row `ssd064`). -/
def parseDefectClass? (model : FlatModel) (group : GroupPath) (language : Language) (text : String)
    (bindingGroup : GroupPath := group) : Option String :=
  match lex language text with
  | .error error => some error.errorClass.code
  | .ok lexemes =>
      match parseLexemesRecording lexemes with
      | (.ok _, _) => none
      | (.error error, completed) =>
          let eventClass : ParseEvent → Option KernelStaticDiagnostic
            | .reference path => referenceResolutionClass? model group path
            | .read reference => referenceReadClass? model group bindingGroup reference
            | .openPath path => openPathClass? model group path
            | .closedCall call => operationCallClass? model group call bindingGroup
          match completed.toList.findSome? eventClass with
          | some diagnostic => some diagnostic.kernelCode
          | none => some error.errorClass.code

end A12Kernel.Dm
