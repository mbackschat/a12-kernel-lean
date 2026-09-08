import A12Kernel.Elaboration.GeneratedRuleIdentity

/-! # Locks on the generated rules' identity

The four kinds and their three projections are read from the Kernel's own generator, which dispatches
each projection over the same closed type in its own switch. The unraised set is an exhaustive search
over the checkout; both are source-derived rather than measured, and the module documentation says so.
-/

namespace A12Kernel.Conformance.GeneratedRuleIdentity

open A12Kernel

/- **Four kinds, four codes, three message keys, two omission classes.** The three counts in one row,
   because it is their disagreement that a consumer has to respect. -/
example :
    (GeneratedRuleKind.all.map (·.formalCode)).eraseDups.length = 4 ∧
      (GeneratedRuleKind.all.map (·.formalMessageKey)).eraseDups.length = 3 ∧
      (GeneratedRuleKind.all.map (·.isOmissionError)).eraseDups.length = 2 := by
  native_decide

/- The exact code vocabulary, in generator order. A consumer reads these off a result, so the spelling
   is the contract — and two of the four are lowerCamel English while the family's neighbours in the
   same constants interface are German. -/
example :
    GeneratedRuleKind.all.map (·.formalCode) =
      ["mandatoryField", "uniqueIndex", "uniqueValue", "solitaryIndex"] := by
  native_decide

/- **The message key groups the two uniqueness kinds together while the omission flag groups the
   mandatory field with the solitary index.** Written as the two groupings side by side, since either
   one alone looks like a partition a consumer could reuse. -/
example :
    (GeneratedRuleKind.all.filter fun k =>
      k.formalMessageKey == GeneratedRuleKind.uniqueIndexField.formalMessageKey) =
        [.uniqueIndexField, .uniqueValue] ∧
      (GeneratedRuleKind.all.filter (·.isOmissionError)) =
        [.mandatoryField, .solitaryIndexField] := by
  native_decide

/- Preliminary is exactly generated, on every kind and on the authored case. -/
example :
    (GeneratedRuleKind.all.map fun k => generatedRuleIsPreliminary (some k)) =
      List.replicate 4 true ∧
    generatedRuleIsPreliminary none = false := by
  native_decide

/- The five declared-and-unused codes, distinct from each other and from the live four. The mandatory
   **group** code is the one worth noticing: it sits beside the live four with a comment calling it an
   auto-generated rule, and no code path names it. -/
example :
    (UnraisedFormalCode.all.map (·.code)).eraseDups.length = 5 ∧
      UnraisedFormalCode.mandatoryGroup.code = "mandatoryGroup" ∧
      (UnraisedFormalCode.all.map (·.code)).filter
        (GeneratedRuleKind.all.map (·.formalCode)).contains = [] := by
  native_decide

end A12Kernel.Conformance.GeneratedRuleIdentity
