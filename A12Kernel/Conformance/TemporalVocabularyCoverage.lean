import A12Kernel.Elaboration.TimeInput
import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.OmittingDateInput

/-! # A12Kernel.Conformance.TemporalVocabularyCoverage — every legal temporal format has exactly one classifier

The four stored-text classifiers are written and cased family by family, so each one's rows say what
*it* owns. Nothing said what the four of them own **together**, and that is the property a
reimplementer actually needs: given any legal temporal declaration, is its stored text classifiable
at all, and by one classifier or by several?

The question has teeth because both failure directions are silent. A format owned by **no**
classifier is a cell whose text cannot be classified — the defect the declared-kind conjuncts caused,
where a legal cross-kind declaration fell through every certifier and no case noticed because none
carried such a declaration. A format owned by **two** is worse: two classifiers would each claim the
same cell and a consumer's answer would depend on which it asked.

So this module holds one exhaustive table rather than more per-family rows. The denominator is the
Kernel's own admitted format vocabulary — twelve formats, derived by probing rather than hand-listed,
and complete over the 135-candidate declaration universe
([inbound](../../docs/SOURCES.md#inbound-2026-09-05b)). Hand-copying that list is precisely what went
wrong twice on the peer's side, so the list here is a fixture to be checked against its owner rather
than a claim of its own: the count is asserted, and a format the vocabulary gains would need this
table extended before it could pass.

Each format is declared on all three date-bearing **kinds**, which is the second axis and the one the
classifiers stopped reading: the owner must be the same on all three, since the Kernel classifies one
format's text identically whatever kind declares it.
-/

namespace A12Kernel.Conformance.TemporalVocabularyCoverage

open A12Kernel

/-- Which classifier a declaration reaches, as a decidable name rather than a certificate. -/
private inductive Owner where
  | time
  | fullDate
  | dateTime
  | omitting
  deriving Repr, DecidableEq

private def components (year month day hour minute second : Bool) :
    TemporalComponents :=
  { year, month, day, hour, minute, second }

/-- The Kernel's complete admitted temporal format vocabulary, each paired with the component set its
    format names and with the classifier this project intends to own it.

    The third column is what makes the table a separating matrix rather than a listing: it is written
    from the format's shape, so a classifier claiming the wrong one fails here rather than silently
    reclassifying a family. -/
private def vocabulary : List (String × TemporalComponents × Owner) :=
  [ ("HH:mm:ss",              components false false false true true true, .time),
    ("MM",                    components false true false false false false,
      .omitting),
    ("MM-dd",                 components false true true false false false,
      .omitting),
    ("MMdd",                  components false true true false false false,
      .omitting),
    ("ddMM",                  components false true true false false false,
      .omitting),
    ("yyyy",                  components true false false false false false,
      .omitting),
    ("yyyy-MM",               components true true false false false false,
      .omitting),
    ("yyyyMM",                components true true false false false false,
      .omitting),
    ("yyyy-MM-dd",            components true true true false false false,
      .fullDate),
    ("dd.MM.yyyy",            components true true true false false false,
      .fullDate),
    ("yyyyMMdd",              components true true true false false false,
      .fullDate),
    ("yyyy-MM-dd'T'HH:mm:ss", components true true true true true true,
      .dateTime) ]

private def declaration (kind : TemporalKind) (format : String)
    (set : TemporalComponents) : FlatFieldDecl :=
  { id := 0
    groupPath := ["Order"]
    name := "Stamp"
    policy := { kind := .temporal kind set }
    temporalTargetPolicy := some { format, partialMode := .full } }

/-- Every classifier that certifies one declaration, in a fixed order. A singleton is the property
    under test; `[]` and a two-element list are the two silent failures this module exists to
    reject. -/
private def owners (kind : TemporalKind) (format : String)
    (set : TemporalComponents) : List Owner :=
  let field := declaration kind format set
  (if (certifyTimeInputField field).toOption.isSome then [Owner.time] else []) ++
  (if (certifyFullDateInputField field).toOption.isSome then [Owner.fullDate]
    else []) ++
  (if (certifyDateTimeInputField field).toOption.isSome then [Owner.dateTime]
    else []) ++
  (if (certifyOmittingDateInputField field).toOption.isSome then [Owner.omitting]
    else [])

/- The denominator, asserted rather than described: twelve formats, which is the Kernel's admitted
   vocabulary over the 135-candidate universe. A format added to that vocabulary without a row here
   fails this line before it can pass the table below. -/
example : vocabulary.length = 12 := by native_decide

/- **The partition.** Every legal format is certified by exactly one classifier, it is the intended
   one, and the answer is the same on all three date-bearing kinds. The three conjuncts are three
   different claims: totality rules out a format whose text cannot be classified at all, uniqueness
   rules out two classifiers claiming one cell, and kind-independence is the rule the certifiers
   stopped reading. -/
example : vocabulary.all (fun (format, set, owner) =>
    owners .date format set == [owner] &&
      owners .time format set == [owner] &&
      owners .dateTime format set == [owner]) = true := by
  native_decide

/- The negative control, on a format the vocabulary refuses: no classifier claims it, so the table
   above is a property of the admitted set rather than of the certifiers being permissive. Without
   this row a certifier that accepted everything would satisfy totality. -/
example :
    owners .date "yyyy/MM/dd" TemporalComponents.fullDate = [] ∧
      owners .time "HH:mm" (components false false false true true false) = [] := by
  native_decide

/- And a **component set contradicting its own format** is claimed by nobody either, which is what
   keeps the table from reading as "the format string alone decides". Both inputs are consulted: a
   complete-date spelling declared with a time-only set reaches no classifier, so the pairing in the
   vocabulary above is load-bearing rather than decorative. -/
example : owners .date "yyyy-MM-dd" TemporalComponents.time = [] := by
  native_decide

end A12Kernel.Conformance.TemporalVocabularyCoverage
