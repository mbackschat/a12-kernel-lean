import A12Kernel.Elaboration.StaticDiagnostic

/-! # What a declared restricted charset may say, and in what order the Kernel objects

A String field may restrict the characters it admits by declaring a **list of entries**, each of which
is a single character, a `a-b` range, or a grapheme built from combining marks. Six refusal classes
guard that list. They are one capsule because they are two stages of one function and the stage split
is itself observable.

**The stages shadow.** Three classes come from the parse stage — a backwards range, an entry that
combines nothing, and the catch-all — and any one of them makes the parse yield nothing. The other
three come from a validate stage that runs the parse first and reads its result, so **no charset ever
reports a class from both stages**. A consumer that gathers all six by running six independent
predicates will report pairs the Kernel cannot.

**Lengths are UTF-16 code units, not code points**, because the Kernel's own tests are `String.length`
and `charAt`. That single fact drives the surrogate class: a supplementary-plane character measures 2,
so it is not "a single character", falls through to the combined-grapheme branch, decomposes into 1
cluster against a length of 2, and is *admitted* by the parse — only to be reported by validate. The
naive code-point reading admits it outright and never reaches the class at all.

**The three shapes are tested in a fixed order and the range test is first**, so a three-unit entry
whose middle unit is a hyphen is a range and can never be a three-character grapheme. That ordering is
not cosmetic: it is what makes `rangeShapeForcesBasicPlane` true, and through it the surrogate class
unreachable for a range.

**`CHARSET_PARSE_ERROR` names a general parse failure and has exactly one trigger**, the empty entry —
proved rather than observed, because the three shape tests between them cover every nonempty string.

Grapheme-cluster decomposition is **an input here, not a derivation**: UAX #29 segmentation is
Unicode's contract rather than A12's, and every gate below reads only the resulting list. Modelling it
would import a specification this project does not own and cannot check.

**Evidence.** `external evidence pending` for the whole family. The mechanism is read from the Kernel's
charset utility and its own documented restrictions; no probe here authors a restricted charset, and
[`docs/IMPLEMENTATION-MAP.md`](../../docs/IMPLEMENTATION-MAP.md) owns that status. This module carries no
rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- The UTF-16 code units of a code-point sequence. A supplementary-plane code point contributes its
surrogate pair, which is the whole reason this is not the code-point count. Written over the list
rather than the `String` so its laws need no reasoning about string representation. -/
def utf16UnitsOf : List Char → List Nat
  | [] => []
  | c :: cs =>
      (if c.val < 0x10000 then [c.val.toNat]
       else [0xD800 + (c.val.toNat - 0x10000) / 0x400, 0xDC00 + (c.val.toNat - 0x10000) % 0x400])
      ++ utf16UnitsOf cs

/-- The UTF-16 code units of a string, which is the sequence the Kernel's length and index tests read. -/
def utf16Units (s : String) : List Nat := utf16UnitsOf s.toList

/-- `String.length` as the Kernel counts it. -/
def utf16Length (s : String) : Nat := (utf16Units s).length

/-- Whether any UTF-16 unit is a surrogate. Nonempty exactly when the string holds a supplementary
code point, since a well-formed Lean `Char` is never itself a lone surrogate. -/
def containsSurrogates (s : String) : Bool :=
  (utf16Units s).any fun u => 0xD800 ≤ u && u ≤ 0xDFFF

/-- The Kernel's shared bound: the longest admitted grapheme, and simultaneously the exact length of a
range definition. The two being equal is what lets one length test serve both, and a consumer that
splits them apart must keep them equal to stay faithful. -/
def maxGraphemeLength : Nat := 3

/-- Which of the three admitted shapes an entry has, or none of them. -/
inductive EntryShape where
  /-- A `a-b` range definition. -/
  | range
  /-- A grapheme longer than one UTF-16 unit. -/
  | combined
  /-- A single UTF-16 unit. -/
  | atomic
  /-- None of the three. -/
  | unparsable
  deriving Repr, DecidableEq

/-- Exactly three UTF-16 units with a hyphen in the middle. Tested **first**, so it wins over the
combined-grapheme reading of the same three units. -/
def isRangeDefinition (s : String) : Bool :=
  utf16Length s == maxGraphemeLength && (utf16Units s)[1]? == some 0x2D

/-- One UTF-16 unit — so a supplementary-plane character is *not* atomic. -/
def isAtomicGrapheme (s : String) : Bool := utf16Length s == 1

/-- Anything nonempty that is not atomic, which is where a supplementary-plane character lands. -/
def isCombinedGrapheme (s : String) : Bool := !isAtomicGrapheme s && s != ""

/-- **The shape cascade, in the Kernel's own order.** -/
def shapeOf (s : String) : EntryShape :=
  if isRangeDefinition s then .range
  else if isCombinedGrapheme s then .combined
  else if isAtomicGrapheme s then .atomic
  else .unparsable

/-- One entry of a declared charset, paired with the grapheme clusters Unicode segmentation assigns it.
The clusters are supplied rather than derived, for the reason the module docstring gives. -/
structure CharsetEntry where
  /-- The declared text. -/
  text : String
  /-- Its grapheme-cluster decomposition, in order. -/
  clusters : List String
  deriving Repr, DecidableEq

/-- A range's two endpoint code points, when the entry really is a range. Total by construction: a
range is three basic-plane code points, so the list pattern is the only reachable one. -/
def rangeEndpoints (s : String) : Option (Nat × Nat) :=
  match s.toList with
  | [a, _, b] => some (a.val.toNat, b.val.toNat)
  | _ => none

/-- **The parse stage's refusal for one entry.** -/
def parseRefusal (e : CharsetEntry) : Option KernelStaticDiagnostic :=
  match shapeOf e.text with
  | .range =>
      match rangeEndpoints e.text with
      | some (a, b) => if a ≤ b then none else some .charsetRangeStartAfterEnd
      | none => none
  | .combined =>
      if e.clusters.length < utf16Length e.text then none
      else some .charsetGraphemeClusterEqualsLength
  | .atomic => none
  | .unparsable => some .charsetParseError

/-- A code-point range, as the parse stage accumulates it. A single character enters as a range of
length one, which is what lets the merge step treat both uniformly. -/
abbrev CodeRange := Nat × Nat

/-- What a successful parse yields: the ranges, and the combined graphemes that are not ranges.
Deliberately **unsimplified** — the validate stage must still be able to report a too-long grapheme
that simplification would have deleted, since an unsimplified charset is what reaches storage. -/
structure ParsedCharset where
  /-- Every single character and range, each as a code-point interval. -/
  ranges : List CodeRange
  /-- Every admitted combined grapheme. -/
  graphemes : List String
  deriving Repr, DecidableEq

/-- Every parse-stage refusal the charset reports, in entry order. -/
def parseRefusals (charset : List CharsetEntry) : List KernelStaticDiagnostic :=
  charset.filterMap parseRefusal

/-- The parse stage over a whole charset: `none` when **any** entry refused, which the Kernel tracks
as one flag set anywhere across the scan rather than as an early return. -/
def parseCharset (charset : List CharsetEntry) : Option ParsedCharset :=
  if !(parseRefusals charset).isEmpty then none
  else
    some {
      ranges := charset.filterMap fun e =>
        match shapeOf e.text with
        | .range => rangeEndpoints e.text
        -- a single character enters as a range of length one, which is what lets the merge step
        -- treat characters and ranges uniformly
        | .atomic => match e.text.toList with
            | [c] => some (c.val.toNat, c.val.toNat)
            | _ => none
        | _ => none
      graphemes := charset.filterMap fun e =>
        match shapeOf e.text with
        | .combined => some e.text
        | _ => none }


/-- Whether a code point falls inside any accumulated range. -/
def rangeSearch (ranges : List CodeRange) (c : Nat) : Bool :=
  ranges.any fun r => r.1 ≤ c && c ≤ r.2

/-- Whether every cluster is already spelled by the charset — a multi-unit cluster by an admitted
grapheme, a single-unit one by a range. Applied to all clusters for the composability filter and to
all **but the last** for the overlap gate, which is what the offset selects. -/
def clustersContained (clusters : List String) (parsed : ParsedCharset) (drop : Nat) : Bool :=
  (clusters.take (clusters.length - drop)).all fun part =>
    if utf16Length part > 1 then parsed.graphemes.contains part
    else match part.toList with
      | [c] => rangeSearch parsed.ranges c.val.toNat
      | _ => true

/-- **The validate stage's per-entry refusals**, which are a list rather than a first hit: one entry
holding a surrogate *and* exceeding the maximum length reports both. -/
def validateEntryRefusals (e : CharsetEntry) : List KernelStaticDiagnostic :=
  (if containsSurrogates e.text then [.charsetContainsSurrogates] else []) ++
  (if maxGraphemeLength < utf16Length e.text then [.charsetGraphemeTooLong] else [])

/-- **The overlap gate.** An entry whose leading clusters are all already in the charset and whose
final cluster begins some *other* admitted grapheme makes a string segmentable two ways. The partner
must differ in length, since an equal-length partner is the same grapheme under simplification. One
refusal is emitted **per partner**, so a single offending entry can report several. -/
def overlapRefusals (charset : List CharsetEntry) (parsed : ParsedCharset) :
    List KernelStaticDiagnostic :=
  charset.flatMap fun e =>
    if shapeOf e.text != .combined || e.clusters.length ≤ 1 then []
    else if !clustersContained e.clusters parsed 1 then []
    else match e.clusters.getLast? with
      | none => []
      | some suffix =>
          parsed.graphemes.filterMap fun g =>
            if utf16Length suffix != utf16Length g && g.startsWith suffix && e.text != g then
              some .charsetGraphemeOverlap
            else none

/-- **The whole model check over a declared charset**, both stages in the Kernel's order. The validate
stage runs only on a charset the parse stage accepted, which is the shadowing this capsule's law pins. -/
def charsetRefusals (charset : List CharsetEntry) : List KernelStaticDiagnostic :=
  match parseCharset charset with
  | none => parseRefusals charset
  | some parsed => charset.flatMap validateEntryRefusals ++ overlapRefusals charset parsed

end A12Kernel
