import A12Kernel.Reference.Dm.Negate
import A12Kernel.Reference.Dm.NonOperation
import A12Kernel.Reference.Dm.Parser

/-! # Locks for printing and negating conditions

The printer is locked by reading its output back to the same tree, over the grammar's grouping
nodes and path forms. The negation is locked against the
[pair grid](../../../evidence/kernel-30.8.1/captures/negation-pair-grid-2026-10-02/request.json):
negating each of its sixteen unguarded originals yields exactly the complement the Kernel ran beside
it, so the Kernel's verdicts for that complement are the negation's own.
-/

namespace A12Kernel.Dm.NegateLocks

open A12Kernel.Dm

private def english (text : String) : Option Expr := (parseText .english text).toOption.map (·.body)

private def roundTrips (language : Language) (text : String) : Bool :=
  match parseText language text with
  | .ok parsed => (parseText language (printText language parsed)).toOption == some parsed
  | .error _ => false

/- Every grouping node and path form reads back from its print, in both languages. -/
example :
    [roundTrips .english "(FieldFilled(A) And FieldFilled(B)) Or [X] > -5",
     roundTrips .english "{[A] + [B]} * 2 ^ 3 - {[C] / 4} >= 1.50",
     roundTrips .english "Sum(Rows*/Amount Having ([$Rows/Kind] == \"x\")) == 0",
     roundTrips .english "[/Order/Lines/Price] != [../..Order/Total]",
     roundTrips .english "[Kind -> Code] == \"A\" And [Rate For \"de\"] < 3",
     roundTrips .english "NumberOfValueInFields(A, B In \"x\", \"y\" @From ../Rows) == 1",
     roundTrips .english "@SuppressWarning(MVK_X) [Start] < Date(2020, 1, 1)",
     roundTrips .english "['And'] == 1 And ['9a'] == 2",
     roundTrips .german "FeldAngegeben(A) Und [Wert] WieMuster \"[0-9]+\""].all id := by
  native_decide

/- Each single-predicate complement is its own inverse, so negating twice restores the predicate. -/
example : complementPairs.all (fun (left, right) =>
    complementId? left == some right && complementId? right == some left) := by
  native_decide

private def negated (text : String) : Option Expr := do
  (negate (← english text)).toOption

/- The sixteen unguarded grid pairs: the negation of each original is the complement the Kernel ran. -/
example :
    [("FieldFilled(A)", "FieldNotFilled(A)"),
     ("AllFieldsFilled(A, B, C)", "NotAllFieldsFilled(A, B, C)"),
     ("AtLeastOneFieldFilled(A, B, C)", "NoFieldFilled(A, B, C)"),
     ("FieldsNotCollectivelyFilled(A, B, C)", "(AllFieldsFilled(A, B, C) Or NoFieldFilled(A, B, C))"),
     ("MoreThanOneFieldFilled(A, B, C)", "NumberOfFilledFields(A, B, C) <= 1"),
     ("NotExactlyOneFieldFilled(A, B, C)", "NumberOfFilledFields(A, B, C) == 1"),
     ("GroupFilled(G)", "GroupNotFilled(G)"),
     ("AllGroupsFilled(G, H)", "NotAllGroupsFilled(G, H)"),
     ("AtLeastOneGroupFilled(G, H)", "NoGroupFilled(G, H)"),
     ("GroupsNotCollectivelyFilled(G, H)", "(AllGroupsFilled(G, H) Or NoGroupFilled(G, H))"),
     ("[A] > 5", "[A] <= 5"), ("[A] == 5", "[A] != 5"),
     ("[S] PatternMatched \"[A-Z]+\"", "[S] PatternViolated \"[A-Z]+\""),
     ("FieldValueIncludedInValueList(S, \"AB\", \"CD\")",
      "FieldValueNotIncludedInValueList(S, \"AB\", \"CD\")"),
     ("[F] == True", "[F] != True"), ("[K] == True", "[K] != True")].all
      (fun (original, complement) => negated original == english complement) := by
  native_decide

/- A guarded pair is not a negation: De Morgan turns the guard into its complement, so the negated
rule also fires where the guard fails, which the grid's guarded complement never does. -/
example :
    negated "FieldFilled(A) And AtLeastOneFieldFilled(Rows*/R)" ==
      english "FieldNotFilled(A) Or NoFieldFilled(Rows*/R)" := by
  native_decide

/- The surface comparison complement is the semantic one, so a negated comparison lowers onto the
operator the pair theorems cover. -/
example :
    [CompareOp.eq, .ne, .lt, .le, .gt, .ge].all fun op =>
      (op.complement?.bind CompareOp.toNumeric?) ==
        (op.toNumeric?.map fun | .ordinary o => .ordinary o.complement | other => other) := by
  native_decide

/- A predicate without a complement refuses the negation with its name. -/
example :
    [(english "DateRangesOverlap(A, B)").map (negate · |>.toOption.isNone),
     (english "FieldFilled(A) And [A] DiffersWithToleranceRange1 [B]").map
       (negate · |>.toOption.isNone)] == [some true, some true] := by
  native_decide

/- `Valid` and `Invalid` are complements in the date form only: with an unregistered type name the
Kernel fires both on every filled field
([supplement](../../../evidence/kernel-30.8.1/captures/negation-pair-supplement-2026-10-02/request-en.json)),
so the field form refuses the negation. -/
example :
    [negated "Valid(Date(D, M, Y))" == english "Invalid(Date(D, M, Y))",
     negated "Invalid(Date(D, M, Y))" == english "Valid(Date(D, M, Y))",
     negated "Valid(S, \"IBAN\")" == none, negated "Invalid(S, \"IBAN\")" == none].all id := by
  native_decide

private def lowered (language : Language) (text : String) : Option Expr := do
  (lowerNon (← (parseNonText language text).toOption).body).toOption

/- A `Non` twin lowers to its predicate's complement wherever it stands, a compound complement keeping
its own bracket, in both languages; a name not followed by `(` stays a name. -/
example :
    [lowered .english "NonFieldFilled(A) And [B] > 1" == english "FieldNotFilled(A) And [B] > 1",
     lowered .english "NonFieldsNotCollectivelyFilled(A, B) Or FieldFilled(C)" ==
       english "(AllFieldsFilled(A, B) Or NoFieldFilled(A, B)) Or FieldFilled(C)",
     lowered .english "NonNoFieldFilled(Rows*/R)" == english "AtLeastOneFieldFilled(Rows*/R)",
     lowered .german "NonFeldAngegeben(A)" == english "FieldNotFilled(A)",
     lowered .english "[NonFieldFilled] == 1" == english "[NonFieldFilled] == 1"].all id := by
  native_decide

/- The twin is the extension's: the Kernel language reads `NonFieldFilled` as a name and refuses the
call, and a predicate without a complement has no twin. -/
example :
    [(parseText .english "NonFieldFilled(A)").toOption.isNone,
     lowered .english "NonFieldValuesNotUnique(A, B)" == none,
     ((parseNonText .english "NonFieldValuesNotUnique(A, B)").toOption.isSome)].all id := by
  native_decide

/- A complement keeps its original's `In` list and `@From` scope, which `NoFieldValueIncludedInValueList`
needs to mean the same members and values. -/
example :
    negated "AtLeastOneFieldValueIncludedInValueList(A, B In \"x\", \"y\" @From ../Rows)" ==
      english "NoFieldValueIncludedInValueList(A, B In \"x\", \"y\" @From ../Rows)" := by
  native_decide

private def nonRoundTrips (language : Language) (text : String) : Bool :=
  match parseNonText language text with
  | .ok parsed => (parseNonText language (printText language parsed)).toOption == some parsed
  | .error _ => false

/- A twin prints in the model's language and reads back to the same tree; a quoted name before `(`
is a name whatever it spells, so it is not read as a twin. -/
example :
    [nonRoundTrips .german "NonFeldAngegeben(A) Und NonAlleFelderAngegeben(A, B)",
     nonRoundTrips .english "NonFieldFilled(A) Or NonNoFieldFilled(B)",
     (parseNonText .english "'NonFieldFilled'(A)").toOption.isNone].all id := by
  native_decide

end A12Kernel.Dm.NegateLocks
