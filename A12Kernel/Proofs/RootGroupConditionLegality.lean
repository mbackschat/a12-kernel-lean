import A12Kernel.Elaboration.RootGroupConditionLegality

/-! # Form- and row-level construct laws

Three results. The construct's class is decided by the model's condition language alone, so neither
the keyword nor its star reaches the answer; the two classes that read the star are therefore
unreachable from an A12 model; and the row family collapses to one class in both languages, which is
the asymmetry that makes the two families worth one module.
-/

namespace A12Kernel

/-- **The star is not read.** Whatever the keyword, the starred and unstarred spellings draw the same
class — which is what makes the two star-reading classes unreachable rather than merely unobserved. -/
@[simp] theorem a12FormConditionRefusal_ignores_wildcard (language : ConditionLanguage)
    (keyword : FormConditionKeyword) (left right : Bool) :
    a12FormConditionRefusal language keyword left =
      a12FormConditionRefusal language keyword right := by
  rfl

/-- The keyword is not read either, so the whole family answers by condition language. -/
theorem a12FormConditionRefusal_ignores_keyword (language : ConditionLanguage)
    (left right : FormConditionKeyword) (starred : Bool) :
    a12FormConditionRefusal language left starred =
      a12FormConditionRefusal language right starred := by
  rfl

/-- **Only two classes are reachable from an A12 document model**, on either family and at either
language. The three the vocabulary also contains belong to the H-model branch. -/
theorem a12FormConditionRefusal_reachable (language : ConditionLanguage)
    (keyword : FormConditionKeyword) (starred : Bool) :
    RootGroupConditionRefusal.reachableFromA12.contains
      (a12FormConditionRefusal language keyword starred) := by
  cases language <;> rfl

/-- The construct's own class arises exactly on the German model, which is the statement that the
diagnostic a consumer sees is a property of the model's configuration rather than of the authored
text. -/
theorem a12FormConditionRefusal_german_iff (language : ConditionLanguage)
    (keyword : FormConditionKeyword) (starred : Bool) :
    a12FormConditionRefusal language keyword starred = .invalidRootGroupConstr ↔
      language = .german := by
  cases language <;> simp [a12FormConditionRefusal]

/-- **The row family is language-independent**, unlike the form family. Stated as an equation between
the two languages rather than as a value, so the contrast with the form family is the content. -/
theorem a12RowConditionRefusal_language_free (left right : ConditionLanguage)
    (keyword : RowConditionKeyword) :
    a12RowConditionRefusal left keyword = a12RowConditionRefusal right keyword := by
  rfl

/-- The row family never reaches its checker, so its argument class cannot fire. -/
theorem a12RowConditionRefusal_never_invalidParams (language : ConditionLanguage)
    (keyword : RowConditionKeyword) :
    a12RowConditionRefusal language keyword ≠ .invalidParamsForOp := by
  simp [a12RowConditionRefusal]

end A12Kernel
