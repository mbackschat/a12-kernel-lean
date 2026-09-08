/-! # A supplied address is checked before its value, and the class names the coordinate's position

Every entry a document supplies passes an **address gate** before the Kernel reads its value: the
coordinate vector is checked against the caps its declaration implies, and then — for a field — the
sub-scope discriminator. Twelve runtime formal codes report the ways that fails, and they are the
codes a `validateFull` consumer actually reads rather than message-bundle keys
([`RuntimeFormalMessageKey`](../Semantics/RuntimeFormalMessageKey.lean) owns the message side).

**The class is chosen by the offending coordinate's *position*, not by what the coordinate means.**
One vector holds one entry per container level on the entity's path, and a field's vector carries one
further entry for the field's own row cap. Position 0 reports the form-serial class, the last position
reports the row class, and everything between reports the context class. That rule has a corner which
is not a detail: **at length 1 position 0 is also the last position, and the serial class wins**,
because the row test lives in a loop that starts at position 1. So the familiar reading "the last
index is the row" is false exactly for a vector of length one — the address of a repeatable **root
group**.

**Consequence, measured.** Over-instantiating a repeatable root group draws the serial class on the
row *and on every node beneath it*, and no row or context class anywhere; over-instantiating any
deeper group draws the row class on that group's own address and the context class on each descendant
([checkpoint](../../docs/SOURCES.md#src-address-index-position-classes)). The same violated level thus
reports under two different codes depending on which address is reporting it, and
[`OverRepetitionFindings`](OverRepetitionFindings.lean) consumes this rule rather than restating it.

**Both minimum tests run before any maximum test.** They are two separate passes over the whole
vector, so an address that is under the minimum at a late position and over the maximum at an early
one reports the *minimum* class of the late position. A consumer that walks the vector once, testing
both bounds at each position, gets a different answer on exactly those addresses.

**The two gates are ordered and a group skips the second.** A failing coordinate vector suppresses the
sub-scope check, and a group-named entry is never sub-scope-checked at all — so no group address can
draw a sub-scope class.

**Evidence.** The three over-maximum classes and their positional split are measured on both codegen
strategies with an accepted control ([checkpoint](../../docs/SOURCES.md#src-address-index-position-classes)).
The under-minimum classes and the index-count class have no witness through the document carrier,
whose coordinates are array positions and therefore never below one or miscounted; they are stated
here as the total function the Kernel computes, with authorability recorded separately and unknown.
Three of the four sub-scope classes are mechanism-derived unreachable in an A12 document model, by
enumerating the one reader of the sub-scope cap.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Where an offending coordinate sits in its own address's vector. The class of the refusal follows
this and nothing else. -/
inductive IndexPosition where
  /-- Position 0 — the form serial number. Wins even when it is also the last position. -/
  | serial
  /-- An interior position: a repeatable container above the reporting entity. -/
  | context
  /-- The last position, when the vector is longer than one. -/
  | row
  deriving Repr, DecidableEq

/-- Classify a position within a vector of the given length. Total, and deliberately independent of
the model: the Kernel's own test is arithmetic on the index alone. -/
def indexPosition (position length : Nat) : IndexPosition :=
  if position == 0 then .serial
  else if position + 1 == length then .row
  else .context

/-- A class the address gate can report. -/
inductive AddressRefusal where
  /-- The supplied name is in neither the field nor the group namespace. -/
  | fieldUnknown
  /-- The vector's length does not match the caps the declaration implies. -/
  | indexCountWrong
  | serialTooSmall
  | serialTooLarge
  | contextTooSmall
  | contextTooLarge
  | rowTooSmall
  | rowTooLarge
  /-- A sub-scope cap is declared and the address supplies none. -/
  | usbMissing
  | usbTooSmall
  | usbTooLarge
  /-- No sub-scope cap is declared and the address supplies one anyway. -/
  | usbUnexpected
  deriving Repr, DecidableEq

namespace AddressRefusal

/-- The exact surfaced code. These are runtime codes, not message-bundle keys: the two vocabularies
differ, and [`RuntimeFormalMessageKey`](../Semantics/RuntimeFormalMessageKey.lean) owns the other. -/
def code : AddressRefusal → String
  | .fieldUnknown => "feldUnbekannt"
  | .indexCountWrong => "falscheAnzahlIndices"
  | .serialTooSmall => "zuKleineLfdNummer"
  | .serialTooLarge => "zuGrosseLfdNummer"
  | .contextTooSmall => "zuKleineKontextnummer"
  | .contextTooLarge => "zuGrosseKontextnummer"
  | .rowTooSmall => "zuKleineZeile"
  | .rowTooLarge => "zuGrosseZeile"
  | .usbMissing => "keinUsbAngegeben"
  | .usbTooSmall => "zuKleinerUsb"
  | .usbTooLarge => "zuGrosserUsb"
  | .usbUnexpected => "usbAngegebenBeiMaxUsbNull"

/-- Every class of the family. -/
def all : List AddressRefusal :=
  [.fieldUnknown, .indexCountWrong, .serialTooSmall, .serialTooLarge, .contextTooSmall,
   .contextTooLarge, .rowTooSmall, .rowTooLarge, .usbMissing, .usbTooSmall, .usbTooLarge,
   .usbUnexpected]

end AddressRefusal

/-- The under-minimum class for a position. -/
def IndexPosition.tooSmall : IndexPosition → AddressRefusal
  | .serial => .serialTooSmall
  | .context => .contextTooSmall
  | .row => .rowTooSmall

/-- The over-maximum class for a position. -/
def IndexPosition.tooLarge : IndexPosition → AddressRefusal
  | .serial => .serialTooLarge
  | .context => .contextTooLarge
  | .row => .rowTooLarge

/-- The first position holding a coordinate below one, if any. -/
def firstBelowMinimum (indices : List Int) : Option Nat :=
  indices.findIdx? (· < 1)

/-- The first position holding a coordinate above its cap, if any. Positions beyond the shorter list
are not examined; the length gate has already rejected a mismatch before this runs. -/
def firstAboveMaximum (indices caps : List Int) : Option Nat :=
  (indices.zip caps).findIdx? fun (index, cap) => index > cap

/-- **The coordinate gate.** Length first, then every minimum, then every maximum — three passes in
that order, each reporting the first position it finds. -/
def indexRefusal (indices caps : List Int) : Option AddressRefusal :=
  if indices.length != caps.length then some .indexCountWrong
  else match firstBelowMinimum indices with
    | some position => some (indexPosition position indices.length).tooSmall
    | none =>
      match firstAboveMaximum indices caps with
      | some position => some (indexPosition position indices.length).tooLarge
      | none => none

/-- The position a violated container level occupies in **its own group's** address. A group's vector
holds one entry per container level on its path, so the group is always its own last position — and at
container depth one that same position is also position 0, where the serial class wins. -/
def violatedLevelOwnPosition (containerDepth : Nat) : IndexPosition :=
  indexPosition (containerDepth - 1) containerDepth

/-- The position a violated container level occupies in the address of anything **strictly beneath**
it, where it can never be the last position. The representative length is one deeper than the level;
[`indexPosition_beyond_depth`](../Proofs/AddressFormalLegality.lean) shows every deeper length agrees. -/
def violatedLevelDescendantPosition (containerDepth : Nat) : IndexPosition :=
  indexPosition (containerDepth - 1) (containerDepth + 1)

/-- What an address supplies for the sub-scope discriminator. Absence is a distinct state rather than
a sentinel number, because both its presence and its absence can be the refused condition. -/
inductive UsbValue where
  | absent
  | supplied (value : Int)
  deriving Repr, DecidableEq

/-- **The sub-scope gate.** A declared cap demands a value in range; no declared cap demands no value.
The two mismatch directions report different classes, which is what lets a consumer say whether the
address or the declaration is the surprise. -/
def usbRefusal (declaredCap : Option Int) (supplied : UsbValue) : Option AddressRefusal :=
  match declaredCap, supplied with
  | some _, .absent => some .usbMissing
  | some cap, .supplied value =>
      if value < 1 then some .usbTooSmall
      else if value > cap then some .usbTooLarge
      else none
  | none, .absent => none
  | none, .supplied _ => some .usbUnexpected

/-- Which namespace the supplied name resolved in. A name that is only a group is admitted as a group
entry, and only when the model does not carry unique entities — otherwise it is unknown. -/
inductive DeclaredAs where
  | field
  | group
  | neither
  deriving Repr, DecidableEq

/-- How one supplied entry is treated after name resolution. -/
inductive AddressKind where
  /-- Checked against the field caps and then sub-scope-checked. -/
  | field
  /-- Checked against the group caps only. -/
  | group
  /-- Deferred and reported at the end of the run, with a rewritten address. -/
  | unknown
  deriving Repr, DecidableEq

/-- Name resolution. The unique-entities flag demotes a group-only name to unknown, so the same model
content is a group entry in one model and an unknown field in another. -/
def resolveEntry (declared : DeclaredAs) (uniqueEntities : Bool) : AddressKind :=
  match declared with
  | .field => .field
  | .group => if uniqueEntities then .unknown else .group
  | .neither => .unknown

/-- **The address gate for one resolved entry**, first-match-wins across both stages. A group entry
never reaches the sub-scope gate, so no group address draws a sub-scope class. -/
def addressRefusal (kind : AddressKind) (indices caps : List Int) (declaredCap : Option Int)
    (supplied : UsbValue) : Option AddressRefusal :=
  match kind with
  | .unknown => some .fieldUnknown
  | .group => indexRefusal indices caps
  | .field =>
      match indexRefusal indices caps with
      | some refusal => some refusal
      | none => usbRefusal declaredCap supplied

/-- The address an unknown-name finding is reported at: every coordinate zeroed, and the sub-scope
discriminator zeroed when the address supplied one at all.

This is not the address the document supplied, and a consumer correlating findings back to input
cells by address will mis-correlate unless it special-cases this class. Absence is preserved, so an
address that supplied no discriminator is still reported without one. -/
def unknownFieldReportedAddress (indices : List Int) (supplied : UsbValue) :
    List Int × UsbValue :=
  (indices.map fun _ => 0,
    match supplied with
    | .absent => .absent
    | .supplied _ => .supplied 0)

/-- The sub-scope cap an **A12 document model** declares, for every entity: none.

The cap is read from one key on the entity's root group, and that key is an Extmp model extension
that an A12 document model never carries — enumerated as the single reader of the cap, whose only
writer is the extension channel. Mechanism-derived, not measured; it is what makes three of the four
sub-scope classes unreachable while leaving the fourth live. -/
def a12DeclaredUsbCap : Option Int := none

end A12Kernel
