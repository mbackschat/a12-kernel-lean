import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Elaboration.LegalCharset — checked supported-character definitions

The caller supplies Java-compatible Unicode grapheme clustering. This module validates the model declaration and lowers it to the platform-independent bounded runtime scanner.
-/

namespace A12Kernel

/-- Definition failures retained by the parser-independent checked boundary. -/
inductive SupportedCharactersDefinitionError where
  | emptyEntry (index : Nat)
  | surrogateBearingEntry (index : Nat)
  | reversedRange (index : Nat)
  | entryTooLong (index : Nat)
  | plainMultiCharacterEntry (index : Nat)
  | ambiguousOverlap (index : Nat)
  deriving Repr, DecidableEq

private structure ParsedLegalCharAtom where
  index : Nat
  sourceText : String
  atom : LegalCharAtom
  clusters : List String

private inductive ParsedSupportedCharacter where
  | range (range : LegalCharRange)
  | atom (atom : ParsedLegalCharAtom)

private def parseSupportedCharacter (clustersOf : String → List String)
    (index : Nat) (entry : String) :
    Except SupportedCharactersDefinitionError ParsedSupportedCharacter :=
  let characters := entry.toList
  if characters.isEmpty then
    .error (.emptyEntry index)
  else if !(characters.all isBmpScalar) then
    .error (.surrogateBearingEntry index)
  else
    match characters with
    | [single] => .ok (.range { first := single, last := single })
    | [first, second] =>
        if (clustersOf entry).length < 2 then
          let parsedAtom : ParsedLegalCharAtom := {
            index := index
            sourceText := entry
            atom := .pair first second
            clusters := clustersOf entry
          }
          .ok (.atom parsedAtom)
        else
          .error (.plainMultiCharacterEntry index)
    | [first, '-', last] =>
        if first.toNat ≤ last.toNat then
          .ok (.range { first := first, last := last })
        else
          .error (.reversedRange index)
    | [first, second, third] =>
        if (clustersOf entry).length < 3 then
          let parsedAtom : ParsedLegalCharAtom := {
            index := index
            sourceText := entry
            atom := .triple first second third
            clusters := clustersOf entry
          }
          .ok (.atom parsedAtom)
        else
          .error (.plainMultiCharacterEntry index)
    | _ => .error (.entryTooLong index)

private def parseSupportedCharacters (clustersOf : String → List String) :
    Nat → List String →
      Except SupportedCharactersDefinitionError
        (List LegalCharRange × List ParsedLegalCharAtom)
  | _, [] => .ok ([], [])
  | index, entry :: remaining => do
      let parsed ← parseSupportedCharacter clustersOf index entry
      let (ranges, atoms) ←
        parseSupportedCharacters clustersOf (index + 1) remaining
      match parsed with
      | .range range => .ok (range :: ranges, atoms)
      | .atom atom => .ok (ranges, atom :: atoms)

private def splitLast : List α → Option (List α × α)
  | [] => none
  | [last] => some ([], last)
  | first :: remaining =>
      match splitLast remaining with
      | none => none
      | some (leading, last) => some (first :: leading, last)

private def clusterRepresentable (ranges : List LegalCharRange)
    (atoms : List ParsedLegalCharAtom) (cluster : String) : Bool :=
  match cluster.toList with
  | [character] => restrictedAllows ranges character
  | characters => atoms.any (fun candidate => candidate.atom.characters == characters)

private def hasAmbiguousOverlap (ranges : List LegalCharRange)
    (atoms : List ParsedLegalCharAtom) (candidate : ParsedLegalCharAtom) : Bool :=
  match splitLast candidate.clusters with
  | none | some ([], _) => false
  | some (leadingClusters, suffix) =>
      leadingClusters.all (clusterRepresentable ranges atoms) &&
        atoms.any (fun other =>
          utf16CodeUnitLength suffix != utf16CodeUnitLength other.sourceText &&
            startsWithCharacters other.sourceText.toList suffix.toList)

private def firstAmbiguousOverlap? (ranges : List LegalCharRange) :
    List ParsedLegalCharAtom → List ParsedLegalCharAtom → Option Nat
  | _, [] => none
  | all, candidate :: remaining =>
      if hasAmbiguousOverlap ranges all candidate then some candidate.index
      else firstAmbiguousOverlap? ranges all remaining

/-- Admit the model's `supportedCharacters` list using one caller-supplied Java-compatible grapheme-cluster classifier. Empty lists select the default; nonempty lists retain only checked ranges and bounded atomic entries. -/
def admitSupportedCharacters (clustersOf : String → List String)
    (entries : List String) :
    Except SupportedCharactersDefinitionError LegalCharset := do
  if entries.isEmpty then
    .ok .defaultBmp
  else
    let (ranges, parsedAtoms) ← parseSupportedCharacters clustersOf 0 entries
    match firstAmbiguousOverlap? ranges parsedAtoms parsedAtoms with
    | some index => .error (.ambiguousOverlap index)
    | none => .ok (.restricted ranges (parsedAtoms.map (·.atom)))

end A12Kernel
