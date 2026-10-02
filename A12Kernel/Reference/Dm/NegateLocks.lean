import A12Kernel.Reference.Dm.Negate
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

end A12Kernel.Dm.NegateLocks
