/-! # The four auto-generated rules, and the three projections that disagree about them

The Kernel generates validation rules from model declarations rather than from authored conditions:
a mandatory field, a repeatable group's index uniqueness, a multi-select group's value uniqueness, and
a solitary index. This module owns the **identity** each generated rule carries — the runtime formal
code a consumer reads, the message-bundle key that renders it, and whether the rule is an omission
error — and nothing about how they evaluate, which
[`CheckedIndexPreliminary`](CheckedIndexPreliminary.lean) already owns.

**The three projections partition the four types differently, and that is the whole point.** The code
separates all four. The message key does not: index uniqueness and value uniqueness share one, so a
consumer keying off the rendered message cannot tell them apart. The omission flag splits the four a
*third* way, pairing the mandatory field with the solitary index — a partition that crosses the
message one. So no two of the three projections can be derived from each other, and a consumer that
infers one from another is wrong in both directions.

**Every generated rule is preliminary**, which is exactly the property that distinguishes it from an
authored one: the generator marks a rule preliminary when and only when it has a generation type.

**Five neighbouring runtime formal codes are declared and never used.** The constants interface also
names an empty-field code, a blank-only-value code, two mandatory-check rule names, and a mandatory
**group** code — the last sitting directly beside the four live ones with a comment calling it an
auto-generated rule. None of the five is referenced anywhere in the checkout outside its own
declaration and the message catalogs, by constant name or as a string literal. They are the runtime
carrier of the vocabulary [`UnraisedDiagnostic`](UnraisedDiagnostic.lean) owns for the parser
catalogs, and the denominator is searched again here rather than inherited across that carrier
([`LF116`](../../docs/LEAN-FINDINGS.md)); like that one, this is a statement about the checkout at its
reviewed revision, not a proof that no configuration emits them.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Why the Kernel generated a rule. The complete generation vocabulary; an authored rule has none of
these, which is what `generatedRuleIsPreliminary` turns on. -/
inductive GeneratedRuleKind where
  /-- A field the model declares mandatory. -/
  | mandatoryField
  /-- A repeatable group's declared index field must be unique across its rows. -/
  | uniqueIndexField
  /-- A multi-select group's value must be unique. -/
  | uniqueValue
  /-- A group's index must be solitary. -/
  | solitaryIndexField
  deriving Repr, DecidableEq

namespace GeneratedRuleKind

def all : List GeneratedRuleKind :=
  [.mandatoryField, .uniqueIndexField, .uniqueValue, .solitaryIndexField]

/-- The runtime formal **code** a consumer reads off the result. Injective over the four kinds, and
the only one of the three projections that is. -/
def formalCode : GeneratedRuleKind → String
  | .mandatoryField => "mandatoryField"
  | .uniqueIndexField => "uniqueIndex"
  | .uniqueValue => "uniqueValue"
  | .solitaryIndexField => "solitaryIndex"

/-- The message-bundle key the rendered text comes from. **Not** injective: the two uniqueness kinds
share one, so the message cannot distinguish them and only the code can. -/
def formalMessageKey : GeneratedRuleKind → String
  | .mandatoryField => "PFLICHT_FELD_FEHLER"
  | .uniqueIndexField | .uniqueValue => "INDEX_FELD_FEHLER"
  | .solitaryIndexField => "SOLITARY_INDEX_FEHLER"

/-- Whether the rule reports an **omission** rather than a conflict. Partitions the four a third way,
pairing the mandatory field with the solitary index — which crosses the message partition, so neither
projection determines the other. -/
def isOmissionError : GeneratedRuleKind → Bool
  | .mandatoryField | .solitaryIndexField => true
  | .uniqueIndexField | .uniqueValue => false

end GeneratedRuleKind

/-- A rule is preliminary exactly when it was generated. Modelled over an optional kind so that the
authored case is representable and the law has something to say. -/
def generatedRuleIsPreliminary (kind : Option GeneratedRuleKind) : Bool :=
  kind.isSome

/-- A runtime formal code that the constants interface declares and no code path in the checkout
references, by constant name or as a literal. -/
inductive UnraisedFormalCode where
  /-- An empty-field code beside the length checks. -/
  | fieldEmpty
  /-- A blank-only-value code beside the leading- and trailing-blank checks, which *are* live. -/
  | valueOnlyBlanks
  /-- The standard rule *name* for mandatory checks, not an error code. -/
  | mandatoryCheckRuleName
  /-- A mandatory-field-absent code. -/
  | mandatoryFieldMissing
  /-- A mandatory **group** code, commented as an auto-generated rule beside the four live ones. -/
  | mandatoryGroup
  deriving Repr, DecidableEq

namespace UnraisedFormalCode

def code : UnraisedFormalCode → String
  | .fieldEmpty => "feldLeer"
  | .valueOnlyBlanks => "wertNurLeerzeichen"
  | .mandatoryCheckRuleName => "pflichtFeldPruefung"
  | .mandatoryFieldMissing => "pflichtFeldNichtVorhanden"
  | .mandatoryGroup => "mandatoryGroup"

def all : List UnraisedFormalCode :=
  [.fieldEmpty, .valueOnlyBlanks, .mandatoryCheckRuleName, .mandatoryFieldMissing, .mandatoryGroup]

end UnraisedFormalCode

end A12Kernel
