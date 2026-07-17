import A12Kernel.Evidence.StringCascadeReplay

/-! # Direct String-cascade replay locks

The input-only scenario matrix is closed independently of the retained output, and the replay projection exposes only public clean/error/delta/value-state observations.
-/

namespace A12Kernel.Evidence.StringCascade.ReplayTest

open A12Kernel.Evidence.StringCascade

private def expectedRequest := ScenarioRequest.expected

private def appliedProjection (value : Option String) : CoreProjection := {
  clean := []
  changed := []
  errors := []
  cleared := []
  applied := [{ pointer := "/Cascade[1]/Mid", value }] }

example : (match expectedRequest.validate with
    | .ok () => true
    | .error _ => false) = true := by
  native_decide

example : (match expectedRequest.cases with
    | first :: rest =>
        ({ expectedRequest with cases := { first with probes := ["/wrong"] } :: rest }).validate
    | [] => .ok ()).isOk = false := by
  native_decide

example : (match expectedRequest.cases.find? (·.caseId == "source-abc-mid-abc") with
    | some case => match case.replay with
      | .ok projection => projection.signatures == [
          "applied|/Cascade[1]/Mid|value|ABC",
          "applied|/Cascade[1]/Out|value|ABC-X",
          "changed|/Cascade[1]/Out|ABC-X",
          "clean|/Cascade[1]/Mid|ABC",
          "clean|/Cascade[1]/Out|ABC-X"]
      | .error _ => false
    | none => false) = true := by
  native_decide

example : (match expectedRequest.cases.find? (·.caseId == "source-abcd-mid-old") with
    | some case => match case.replay with
      | .ok projection => projection.signatures == [
          "applied|/Cascade[1]/Mid|no-value",
          "applied|/Cascade[1]/Out|no-value",
          "cleared|/Cascade[1]/Out",
          "error|/Cascade[1]/Mid|ABCD|stringZuLang|VALUE_ERROR|/Cascade[1]/Mid"]
      | .error _ => false
    | none => false) = true := by
  native_decide

example : (appliedProjection none).signatures !=
    (appliedProjection (some "")).signatures := by
  native_decide

end A12Kernel.Evidence.StringCascade.ReplayTest
