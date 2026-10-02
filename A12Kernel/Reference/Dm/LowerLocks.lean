import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Parser

/-! # Locks for the leaf carrier dispatch

`lowerCondition` offers each leaf to its carriers in order, so a carrier can be unreachable when an
earlier pattern claims its shape. Each case pins one shape to the carrier that must admit it.
-/

namespace A12Kernel.Dm.LowerLocks

open A12Kernel A12Kernel.Dm

private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order"], name := "Ref", policy := { kind := .string } },
      { id := 3, groupPath := ["Order", "Head"], name := "Code", policy := { kind := .string } },
      { id := 2, groupPath := ["Order", "Rows"], name := "Note", policy := { kind := .string },
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 5 }] }

private def admitted (text : String) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] false parsed.body).toOption.isSome
  | .error _ => false

/- A one-operand group-list quantifier reaches the group-list carrier rather than stopping at the
one-argument presence arm, which admits only `FieldFilled` and `GroupFilled` forms. -/
example :
    [admitted "NoGroupFilled(Rows*)", admitted "AtLeastOneGroupFilled(Rows*)",
     admitted "FieldFilled(Ref)", admitted "GroupFilled(Rows)"].all id := by
  native_decide

/- A category projects a field's value; on a group operand it has nothing to project, so the operand
is refused rather than read as the bare group. -/
example :
    [admitted "AtLeastOneFieldFilled(Head)", !admitted "AtLeastOneFieldFilled(Head -> Code)"].all id := by
  native_decide

/- A count compared with a fractional threshold is refused, where the carrier would read `1.5` as an
integral literal. -/
example :
    [admitted "NumberOfFilledFields(Head) < 2", !admitted "NumberOfFilledFields(Head) < 1.5"].all id := by
  native_decide

private def ruleAt (errorPath : String) : DmRule :=
  { group := ["Order"], name := "R", errorEntityRelPath := errorPath, errorCode := "E"
    condition := "FieldFilled(Ref)", severity := "ERROR" }

/- An error path is written one step below the rule group; one without that step is refused rather
than read at the group, while the written form resolves. -/
example :
    let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [(checkRule dm .english (ruleAt "../Ref")).toOption.isSome,
     (checkRule dm .english (ruleAt "Ref")).toOption.isNone].all id := by
  native_decide

private def ancestorModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "Outer"], name := "Marker", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 2, groupPath := ["Probe", "Outer", "Flat"], name := "A", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 3, groupPath := ["Probe", "Outer", "Peer"], name := "B", policy := { kind := .string },
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Outer"], repeatability := some 3 }] }

/- A group count over fixed groups below the rule's repeatable row lowers onto a carrier the row
iteration runs, as the Kernel evaluates it per row
([capture](../../../evidence/kernel-30.8.1/captures/fixed-group-repeatable-ancestor-carriers/request.json)). -/
example :
    let dm : DmModel := { flat := ancestorModel, rules := [], computations := [],
                          conditionLanguage := "en_US", refusals := [] }
    let rule : DmRule := { group := ["Probe", "Outer"], name := "R", errorEntityRelPath := "../Marker"
                           errorCode := "E", severity := "ERROR"
                           condition := "FieldFilled(Marker) And NumberOfFilledGroups(Flat, Peer) == 2" }
    ((checkRule dm .english rule).toOption.map (·.condition.core.supportsOrdinaryIteration)) ==
      some true := by
  native_decide

end A12Kernel.Dm.LowerLocks
