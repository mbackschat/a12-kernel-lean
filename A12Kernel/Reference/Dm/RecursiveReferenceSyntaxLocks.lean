import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Print

/-! # Recursive entity-reference syntax locks

The reference grammar in [spec §7.3](../../../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)
owns attachments even when a later static check refuses them. Exact trees separate recursive key
ownership from a flattened path or a filter stored on the call argument.
-/

namespace A12Kernel.Dm.RecursiveReferenceSyntaxLocks

private def body (language : Language) (source : String) : Option Expr :=
  (parseText language source).toOption.map (·.body)

private def reference (segments : List (String × Bool)) : Reference :=
  { path := { segments := segments.map fun (name, star) => { name, star } } }

private def plain (names : List String) : Reference := reference (names.map (·, false))

private def enabled (group : String) : Expr :=
  .compare .eq (.value (plain [group, "Enabled"])) (.constant "True")

private def positive (group : String) : Expr :=
  .compare .gt (.value (plain [group, "N"])) (.number "0")

private def sumPositive (target : Reference) : Expr :=
  .compare .gt (.call "Sum" [.mk (.entity target) none] none none) (.number "0")

private def rowsN : Reference := reference [("Rows", true), ("N", false)]

private def roundTrips (language : Language) (source : String) : Bool :=
  match parseText language source with
  | .error _ => false
  | .ok parsed => (parseText language (printText language parsed)).toOption == some parsed

example : [
    "[Rows/N For Keys/Id For \"x\"] > 0",
    "[Rows/Tag -> Label For \"x\"] == \"K\"",
    "[Rows/N For Keys/Id -> Label] > 0",
    "Sum(Rows*/N For Keys*/Id Having [Keys/Enabled] == True) > 0",
    "[Rows*/N Having [Rows/N] > 0] > 0",
    "RepetitionNotUnique(Rows/N @From Rows For \"x\")",
    "RepetitionNotUnique(Rows/N @From Rows* Having [Rows/N] > 0)"].all
      (roundTrips .english) = true := by native_decide

example : roundTrips .german
    "Summe(Rows*/N Fuer Keys*/Id Mit [Keys/Enabled] == Wahr) > 0" = true := by native_decide

example :
    body .english "Sum(Rows*/N For Keys*/Id Having [Keys/Enabled] == True) > 0" ==
      some (sumPositive { rowsN with index := some (.reference
        { reference [("Keys", true), ("Id", false)] with filter := some (enabled "Keys") }) }) := by
  native_decide

example :
    body .english "Sum(Rows*/N For \"x\" Having [Rows/N] > 0) > 0" ==
      some (sumPositive { rowsN with index := some (.literal "x"), filter := some (positive "Rows") }) := by
  native_decide

example :
    body .english "[Rows/N For Keys/Id For Gate*/Id Having [Gate/Enabled] == True] > 0" ==
      some (.compare .gt (.value { plain ["Rows", "N"] with index := some (.reference
        { plain ["Keys", "Id"] with index := some (.reference
          { reference [("Gate", true), ("Id", false)] with filter := some (enabled "Gate") }) }) })
        (.number "0")) := by
  native_decide

example :
    [body .english "[Rows/Tag -> Label For Keys/Id] == \"K\"" ==
      some (.compare .eq (.value { plain ["Rows", "Tag"] with
        category := some "Label"
        index := some (.reference (plain ["Keys", "Id"])) }) (.string "K")),
     body .english "[Rows/Tag For Keys/Id -> Label] == \"K\"" ==
      some (.compare .eq (.value { plain ["Rows", "Tag"] with index := some (.reference
        { plain ["Keys", "Id"] with category := some "Label" }) }) (.string "K")),
     body .english "[Rows/Tag -> Label For Keys/Id -> Label For \"x\"] == \"K\"" ==
      some (.compare .eq (.value { plain ["Rows", "Tag"] with
        category := some "Label"
        index := some (.reference { plain ["Keys", "Id"] with
          category := some "Label"
          index := some (.literal "x") }) }) (.string "K")),
     (parseText .english "[Rows/Tag For \"x\" -> Label] == \"K\"").toOption.isNone].all id := by
  native_decide

example :
    [body .english "RepetitionNotUnique(Rows/N @From Rows* -> Label For \"x\" Having [Rows/N] > 0)" ==
      some (.call "RepetitionNotUnique" [.mk (.entity (plain ["Rows", "N"])) none] none
        (some { reference [("Rows", true)] with
          category := some "Label"
          index := some (.literal "x")
          filter := some (positive "Rows") })),
     body .english "RepetitionNotUnique(Rows/N @From Rows For Keys*/Id Having [Keys/Enabled] == True)" ==
      some (.call "RepetitionNotUnique" [.mk (.entity (plain ["Rows", "N"])) none] none
        (some { plain ["Rows"] with index := some (.reference
          { reference [("Keys", true), ("Id", false)] with filter := some (enabled "Keys") }) }))].all id := by
  native_decide

example :
    body .english "[Rows*/N Having [Rows/N] > 0] > 0" ==
      some (.compare .gt (.value { rowsN with filter := some (positive "Rows") }) (.number "0")) := by
  native_decide

example :
    [body .german "Summe(Rows*/N Fuer Keys*/Id Mit [Keys/Enabled] == Wahr) > 0" ==
      some (sumPositive { rowsN with index := some (.reference
        { reference [("Keys", true), ("Id", false)] with filter := some (enabled "Keys") }) }),
     body .german "WiederholungNichtEindeutig(Rows/N @Von Rows* -> Label Fuer \"x\" Mit [Rows/N] > 0)" ==
      body .english "RepetitionNotUnique(Rows/N @From Rows* -> Label For \"x\" Having [Rows/N] > 0)"].all id := by
  native_decide

example :
    let legal (source : String) (inCondition : Bool := true) :=
      (body .english source).map (·.parensLegal inCondition) == some true
    [legal "Sum(Rows*/N For Keys*/Id Having ([Keys/Enabled] == True))" false,
     legal "[Rows/N For Keys/Id For Gate*/Id Having ([Gate/Enabled] == True)]" false,
     legal "RepetitionNotUnique(Rows/N @From Rows* Having ([Rows/N] > 0))" false,
     legal "[Rows*/N Having ([Rows/N] > 0)]" false,
     !legal "Sum(Rows*/N For Keys*/Id Having ([Keys/Enabled]) == True)",
     !legal "[Rows/N For Keys/Id For Gate*/Id Having [Gate/Enabled] == (True)]",
     !legal "RepetitionNotUnique(Rows/N @From Rows* Having [Rows/N] > (0))",
     !legal "[Rows*/N Having [Rows/N] + (1) > 0]"].all id := by
  native_decide

example :
    [body .english "[Rows/N] > 0" == some (positive "Rows"),
     body .english "Sum(Rows*/N) > 0" == some (sumPositive rowsN),
     body .english "Sum(Rows*/N For \"x\") > 0" ==
      some (sumPositive { rowsN with index := some (.literal "x") }),
     body .english "[Rows/N For Keys/Id] > 0" ==
      some (.compare .gt (.value { plain ["Rows", "N"] with
        index := some (.reference (plain ["Keys", "Id"])) }) (.number "0"))].all id := by
  native_decide

example :
    ["[Rows/N] > 0", "Sum(Rows*/N) > 0", "Sum(Rows*/N For \"x\") > 0",
     "Sum(Rows*/N For \"x\" Having [Rows/N] > 0) > 0",
     "[Rows/N For Keys/Id For Gate*/Id Having [Gate/Enabled] == True] > 0",
     "[Rows/Tag -> Label For Keys/Id -> Label For \"x\"] == \"K\"",
     "RepetitionNotUnique(Rows/N @From Rows* -> Label For \"x\" Having [Rows/N] > 0)"].all
       (roundTrips .english) = true := by native_decide

end A12Kernel.Dm.RecursiveReferenceSyntaxLocks
