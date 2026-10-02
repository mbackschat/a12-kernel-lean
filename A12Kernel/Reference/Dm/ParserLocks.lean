import A12Kernel.Reference.Dm.Parser

/-! # Locks for the condition and operation grammar

Each case locks one syntactic law of [`spec/12-concrete-syntax.md`](../../../spec/12-concrete-syntax.md)
against the nearest wrong reading: a case-folding or union-vocabulary lexer, a depth-counting
connective check, a comment treated as trivia, a sign accepted on a reference, a platform whitespace
class. The parse of every retained Kernel text is the replay's lock, not this module's.
-/

namespace A12Kernel.Dm.ParserLocks

open A12Kernel.Dm

private def english (text : String) : Option Expr := (parseText .english text).toOption.map (·.body)

private def refusal (language : Language) (text : String) : Option SyntaxErrorClass :=
  match parseText language text with
  | .ok _ => none
  | .error error => some error.errorClass

private def entity (names : List String) : Expr :=
  .entity { path := { segments := names.map ({ name := ·, star := false }) } }

private def filled (name : String) : Expr := .call "FieldFilled" [.mk (entity [name]) none none] none none

/- One connective per bracket pair, any number of parts; mixing is refused and a parenthesised mixed
part is admitted, so the check is per pair and not per depth. -/
example :
    [english "FieldFilled(A) And FieldFilled(B) And FieldFilled(C)" ==
      some (.logic .and [filled "A", filled "B", filled "C"]),
     refusal .english "FieldFilled(A) And FieldFilled(B) Or FieldFilled(C)" == some .bracketMissing,
     english "(FieldFilled(A) And FieldFilled(B)) Or FieldFilled(C)" ==
      some (.logic .or [.parens (.logic .and [filled "A", filled "B"]), filled "C"])].all id := by
  native_decide

/- Keyword case is enumerated, not folded: `and` joins, `aNd` and `fieldfilled` are names, and a name
before `(` is the token class. -/
example :
    [english "FieldFilled(A) and FieldFilled(B)" == some (.logic .and [filled "A", filled "B"]),
     refusal .english "FieldFilled(A) aNd FieldFilled(B)" == some .unexpectedToken,
     refusal .english "fieldfilled(A)" == some .unexpectedToken].all id := by
  native_decide

/- One vocabulary per model: `Und` joins in German and is a name in English, `And` the reverse. -/
example :
    [(parseText .german "FeldAngegeben(A) Und FeldAngegeben(B)").toOption.map (·.body) ==
      some (.logic .and [filled "A", filled "B"]),
     refusal .english "FieldFilled(A) Und FieldFilled(B)" == some .unexpectedToken,
     refusal .german "FeldAngegeben(A) And FeldAngegeben(B)" == some .unexpectedToken].all id := by
  native_decide

/- A comment is placed, not skipped: admitted around a branch and after `+`, refused inside an argument
list. -/
example :
    [english ";; lead\nFieldFilled(A) ;; tail\nAnd FieldFilled(B)" ==
      some (.logic .and [filled "A", filled "B"]),
     (english "[A] > [B] + ;; note\n 1").isSome,
     refusal .english "FieldFilled(;; note\nA)" == some .unexpectedToken].all id := by
  native_decide

/- A sign stands on a number literal only, and whitespace may stand inside the literal. -/
example :
    [english "[A] > - 2 . 5" == some (.compare .gt (.value { path := { segments := [{ name := "A", star := false }] } })
      (.number "-2.5")),
     refusal .english "[A] > -[B]" == some .unexpectedToken].all id := by
  native_decide

/- Only five whitespace characters separate tokens; a no-break space is a lexer error, and `#Zeile`
lexes in English to be refused by the grammar. -/
example :
    [refusal .english "FieldFilled(A)\u00A0And FieldFilled(B)" == some .lexer,
     refusal .english "#Zeile" == some .unexpectedToken,
     refusal .english "#Zeil" == some .lexer].all id := by
  native_decide

/- A call keeps its operator-specific attachments as written: a filter on a starred argument, the `In`
separator and an `@From` scope. -/
example :
    [english "Sum(Items*/Count Having [Items/Kind] == \"x\") > 0" == some (.compare .gt
      (.call "Sum" [.mk (.entity { path := { segments := [{ name := "Items", star := true },
          { name := "Count", star := false }] } }) none
        (some (.compare .eq (.value { path := { segments := [{ name := "Items", star := false },
          { name := "Kind", star := false }] } }) (.string "x")))] none none)
      (.number "0")),
     english "NumberOfValueInFields(0 In A, B) > 0" == some (.compare .gt
      (.call "NumberOfValueInFields" [.mk (.number "0") none none]
        (some [.mk (entity ["A"]) none none, .mk (entity ["B"]) none none]) none) (.number "0")),
     english "RepetitionNotUnique(Items/Sku @From Items)" == some (.call "RepetitionNotUnique"
      [.mk (entity ["Items", "Sku"]) none none] none
      (some { segments := [{ name := "Items", star := false }] }))].all id := by
  native_decide

/- The H-model constructs are keywords in a German model only: `[ZeilenLueckenlos]` is no field read
there, while an English model reads the same spelling as a name. -/
example :
    [keywordId? .german "VordruckAngegeben" == some "VordruckAngegeben",
     keywordId? .english "VordruckAngegeben" == none,
     (parseText .german "[ZeilenLueckenlos] > 0").toOption.isNone,
     (parseText .english "[ZeilenLueckenlos] > 0").toOption.isSome].all id := by
  native_decide

/- Parentheses group conditions only: around a comparison side, an operation or an argument they are
illegal, while a parenthesised condition and a braced operation are not. -/
example :
    let legal (text : String) := ((parseText .english text).toOption.map (·.body.parensLegal true)) == some true
    [legal "(FieldFilled(A) Or FieldFilled(B)) And [C] > 1", legal "[A] > {[B] + 1}",
     legal "Sum(Rows*/A Having ([$Rows/K] == 1)) > 0",
     !legal "([A]) > 1", !legal "[A] > ([B])", !legal "Sum((Rows*/A)) > 0",
     !legal "Max(([A] > 1), 2) > 0"].all id := by
  native_decide

end A12Kernel.Dm.ParserLocks
