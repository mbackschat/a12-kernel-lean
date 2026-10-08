import A12Kernel.Elaboration.RootGroupConditionLegality

/-! # Locks on the form- and row-level construct refusals

Every row is a measured cell: six form keywords × two star spellings × two condition languages, three
row keywords, and an accepted control in each language
([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs)).
-/

namespace A12Kernel.Conformance.RootGroupConditionLegality

open A12Kernel

/- **The same construct draws two different classes on two models differing only in condition
   language.** On the English model the keyword does not lex and the diagnostic is the generic token
   one; on the German model it reaches the checker and names the construct. A consumer reading only
   the English answer cannot tell this construct from a misspelling. -/
example :
    a12FormConditionRefusal .english .rootGroupSpecified false = .unexpectedToken ∧
      a12FormConditionRefusal .german .rootGroupSpecified false = .invalidRootGroupConstr := by
  native_decide

/- **All six keywords, both star spellings, on the German model: the construct class every time.**
   This is the shadowing measurement — the star is what the two suppressed classes read, so a starred
   and an unstarred row drawing the same class is what shows neither of them runs. -/
example :
    (FormConditionKeyword.all.flatMap fun keyword =>
      [a12FormConditionRefusal .german keyword false,
       a12FormConditionRefusal .german keyword true]) =
      List.replicate 12 RootGroupConditionRefusal.invalidRootGroupConstr := by
  native_decide

/- The two suppressed classes are never produced, whatever the keyword, star, or language — including
   for the two keywords whose H-model branch would require a star. Without this row the family's
   vocabulary would look four-valued where an A12 model sees two. -/
example :
    (FormConditionKeyword.all.flatMap fun keyword =>
      [ConditionLanguage.english, .german].flatMap fun language =>
        [false, true].map fun starred =>
          a12FormConditionRefusal language keyword starred).all
      (RootGroupConditionRefusal.reachableFromA12.contains ·) := by
  native_decide

/- The two keywords that would require a star upstream are distinguished in the model and make no
   difference to the answer, which is the fact the shadowing rests on rather than an accident of the
   fixture. -/
example :
    (FormConditionKeyword.all.filter (·.requiresWildcardInHModel)).length = 2 ∧
      a12FormConditionRefusal .german .noRootGroupSpecified true =
        a12FormConditionRefusal .german .rootGroupSpecified true := by
  native_decide

/- **The row-level family does not lex in either language**, so it is refused one stage earlier than
   the form family and its checker's class never fires. This is the asymmetry: two H-model construct
   families, one reaching a checker and one not. -/
example :
    (RowConditionKeyword.all.flatMap fun keyword =>
      [a12RowConditionRefusal .english keyword, a12RowConditionRefusal .german keyword]) =
      List.replicate 6 RootGroupConditionRefusal.unexpectedToken := by
  native_decide

/- Five distinct keys, of which an A12 model can draw two. The three it cannot are named so a consumer
   implementing this surface knows the vocabulary is larger than what it will observe. -/
example :
    (RootGroupConditionRefusal.all.map (·.catalogKey)).eraseDups.length = 5 ∧
      RootGroupConditionRefusal.reachableFromA12.length = 2 ∧
      (RootGroupConditionRefusal.all.filter
        (!RootGroupConditionRefusal.reachableFromA12.contains ·)).map (·.catalogKey) =
        ["MVK_CONDITION_WITH_WILDCARD", "MVK_CONDITION_WITHOUT_REPEATABLE_ROOTGROUP",
         "MVK_INVALID_PARAMS_FOR_OP"] := by
  native_decide

end A12Kernel.Conformance.RootGroupConditionLegality
