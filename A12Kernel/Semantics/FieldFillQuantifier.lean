/-! # Field-fill quantifier vocabulary

The validation and computation phases share these seven language-level operators. Their evaluators remain separate because validation observes an extensional tally and a collapsed result, while computation performs ordered, poison-preserving scans.
-/

namespace A12Kernel

/-- The seven field-fill operators admitted by the resolved validation and computation capsules. -/
inductive FieldFillQuantifier where
  | allFieldsFilled
  | noFieldFilled
  | atLeastOneFieldFilled
  | moreThanOneFieldFilled
  | notAllFieldsFilled
  | notExactlyOneFieldFilled
  | fieldsNotCollectivelyFilled
  deriving Repr, DecidableEq

end A12Kernel
