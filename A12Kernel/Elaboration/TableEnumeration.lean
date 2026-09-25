import A12Kernel.Elaboration.StaticDiagnostic

/-! # `ValueNotConsistent` and the table enumeration it needs, which an A12 document model never has

A **table enumeration** is an enumeration whose values live in an external data table rather than in the model: the declaration names a table, a key column, and a list of *dependent* columns. The `ValueNotConsistent` condition exists for it and for nothing else — it asks whether a field's value is inconsistent with the values of the columns its table declares as dependent, so the whole construct is meaningless for an enumeration whose values are written out in the model.

**The load-bearing fact is a constant.** An A12 document model's enumeration declaration reports no table name, no column name, and no dependent columns, whatever the model says; the Kernel's table-enumeration predicate is exactly "a table name is present". So in an A12 model no enumeration is a table enumeration, and the construct's table check refuses every field that reaches it. `ValueNotConsistent` parses, elaborates, and is then rejected — always, on any operand, in any model of this kind.

That single constant decides the whole family, so the classes below split into one a consumer will meet and four it will not:

1. **The operand must be a field, carry no wildcard, and be a table enumeration.** The first two answer in the shared operand classes rather than in this family's, each ahead of the third: a non-repeating group draws `MVK_NO_GROUPS_ALLOWED` and a starred selector `MVK_NO_WILDCARDS_ALLOWED`. A field clearing them meets the third arm, measured on an Enumeration, a String and a Number field. All three arms are measured, each against the table check only; no starred group places the first two against each other, and this module asks the field arm first.
2. **The parameter count must equal the declared dependent-column count.** Unreachable behind arm 1; and the declared count is itself always zero here.
3. **Each parameter must be an enumeration.** Unreachable behind arm 1.
4. **Each parameter's value must appear in its dependent column** — one class for a string literal, another for an enumeration whose value set is not contained in the column's. Unreachable behind arm 1, and additionally behind a second constant: the check runs only when the declaration carries *table data*, which no A12 declaration does either.

A fifth class belongs to the same constant from the other side. The ordinary field-value operator refuses a table enumeration outright, so `invalidTableEnum` is the mirror of `tableEnumExpected`: one fires when an operand is not a table enumeration and the other when it is, and in an A12 model the first always fires and the second never can.

**Why model a construct that cannot succeed.** A consumer enumerating the catalogs meets all six keys and cannot tell from the catalog which it will ever see. An importer reading a model that came from elsewhere needs to know that a `ValueNotConsistent` rule is not a rule it failed to understand but one the Kernel itself rejects. And the constant is a *version* fact about the A12 mapping, not a law of the language: the accessor's own neighbours in the Kernel's tool API are not constant, so a later model version could make four of these live without any change to the condition's semantics. Recording the gate in full is what makes that change cheap to absorb.

**Evidence.** `tableEnumExpected` is measured on an ordinary two-value enumeration ([checkpoint](../../docs/SOURCES.md#src-table-enumeration-inertness)), and a12-dmkits measures it on a String and a Number field too, beside the two shape classes ([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-gate-raise-points)). The other four rest on the constant, established by enumerating every implementation of the table-name accessor reachable from an A12 document model — there is exactly one, and it returns absence unconditionally. That is a mechanism claim discharged by exhaustive implementation search, not a measured one, and it is marked as such in the coverage record.

Two refusals ahead of the whole gate are not modelled here, because they belong to reading the operand rather than to this operator: an unstarred repeatable group draws the walk's `MVK_NO_WILDCARD`, and a name resolving to nothing `MVK_INVALID_ENTITY`, both measured on the same lock.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A refusal from the table-enumeration construct and its mirror in the field-value operator. -/
inductive TableEnumRefusal where
  /-- The operand of `ValueNotConsistent` is not a table enumeration. -/
  | tableEnumExpected
  /-- The operand of the ordinary field-value operator *is* a table enumeration. -/
  | invalidTableEnum
  /-- The parameter list's length differs from the declared dependent-column count. -/
  | dependentColumnSizeMismatch
  /-- A parameter is not of enumeration type. -/
  | onlyEnumsAllowed
  /-- A string-literal parameter's value does not occur in its dependent column. -/
  | stringValueNotInColumn
  /-- An enumeration parameter admits a value its dependent column does not. -/
  | enumValuesNotInColumn
  deriving Repr, DecidableEq

namespace TableEnumRefusal

/-- The exact catalog key, which is also the code a static check surfaces. -/
def catalogKey : TableEnumRefusal → String
  | .tableEnumExpected => "MVK_TABLE_ENUM_EXPECTED"
  | .invalidTableEnum => "MVK_INVALID_TABLE_ENUM"
  | .dependentColumnSizeMismatch => "MVK_DEPENDENT_COLUMN_SIZE_MISMATCH"
  | .onlyEnumsAllowed => "MVK_ONLY_ENUMS_ALLOWED"
  | .stringValueNotInColumn => "MVK_STRING_VALUE_NOT_IN_COLUMN"
  | .enumValuesNotInColumn => "MVK_ENUM_VALUES_NOT_IN_COLUMN"

/-- Every class of this family, in the order the construct's own checks can report them. The
mirror class sits last because it belongs to a different operator. -/
def all : List TableEnumRefusal :=
  [.tableEnumExpected, .dependentColumnSizeMismatch, .onlyEnumsAllowed,
   .stringValueNotInColumn, .enumValuesNotInColumn, .invalidTableEnum]

end TableEnumRefusal

/-- One dependent column of an enumeration's backing table. An empty value set means the column
does not exist in the table, which the Kernel treats as "stop checking" rather than as a refusal. -/
structure EnumerationTableColumn where
  name : String
  allowedValues : List String := []
  deriving Repr, DecidableEq

/-- An enumeration declaration as the table-enumeration checks read it.

`tableName` is the whole predicate: the Kernel's table-enumeration test is its presence and nothing
else. `table` is separate and gates only the column checks, so a declaration can name a table whose
data is unavailable and still pass the table check. -/
structure TableEnumerationDeclaration where
  /-- The enumeration's own values, as declared. -/
  values : List String := []
  /-- The backing table's name. Presence of this field *is* being a table enumeration. -/
  tableName : Option String := none
  /-- The key column's name. Read by no check modelled here. -/
  columnName : Option String := none
  /-- The columns whose values a `ValueNotConsistent` parameter list must match, positionally. -/
  dependentColumns : List String := []
  /-- The backing table's data, when known. Absent data skips the column checks entirely. -/
  table : List EnumerationTableColumn := []
  /-- Whether the table's data is available at all, kept separate from an empty table so that
  "no data" and "a table with no columns" stay distinguishable. -/
  tableAvailable : Bool := false
  deriving Repr, DecidableEq

/-- The Kernel's table-enumeration predicate, in full: a table name is present. -/
def isTableEnumeration (declaration : TableEnumerationDeclaration) : Bool :=
  declaration.tableName.isSome

/-- The table view an **A12 document model**'s enumeration presents, whatever the model file says.

[`Enumeration.lean`](Enumeration.lean)'s `EnumerationDeclaration` is the closed A12 declaration and
stays free of these fields deliberately: they are always absent there, and carrying an always-empty
concern in a live type would cost every consumer of it. This function is the bridge, and it supplies
no table name, no key column, no dependent columns, and no table data; only the declared values
survive. It is one accessor's constant answer, and every claim in this module about what an A12
model cannot reach reduces to it. -/
def a12TableView (values : List String) : TableEnumerationDeclaration :=
  { values := values }

/-- What one `ValueNotConsistent` parameter is. -/
inductive TableConsistencyParameter where
  /-- A field of enumeration type, with its declared value set. -/
  | enumerationField (values : List String)
  /-- A quoted string constant. -/
  | stringLiteral (value : String)
  /-- Anything else — a field of another type, or a non-field. -/
  | otherKind
  deriving Repr, DecidableEq

/-- The operand of `ValueNotConsistent`, reduced to what its three checks read. -/
structure TableConsistencyOperand where
  /-- `false` for a group. -/
  isField : Bool := true
  hasWildcard : Bool := false
  declaration : TableEnumerationDeclaration
  deriving Repr, DecidableEq

/-- A refusal of `ValueNotConsistent`, in the order its checks run. The two operand-shape classes
belong to the shared operand checks and keep their own classes, so they are not members of
`TableEnumRefusal`, whose vocabulary is this family's alone. -/
inductive ValueNotConsistentRefusal where
  /-- The operand is a group. -/
  | groupOperand
  /-- The operand carries a wildcard. -/
  | wildcardOperand
  /-- This family's own chain refused the field. -/
  | family (refusal : TableEnumRefusal)
  deriving Repr, DecidableEq

/-- The exact catalog key. -/
def ValueNotConsistentRefusal.catalogKey : ValueNotConsistentRefusal → String
  | .groupOperand => KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  | .wildcardOperand => KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  | .family refusal => refusal.catalogKey

/-- One parameter checked against its dependent column. The column's empty value set means the
column is absent from the table, and the Kernel then checks nothing rather than refusing. -/
def parameterValueRefusal (parameter : TableConsistencyParameter) (column : EnumerationTableColumn) :
    Option TableEnumRefusal :=
  if column.allowedValues.isEmpty then
    none
  else
    match parameter with
    | .stringLiteral value =>
        if column.allowedValues.contains value then none else some .stringValueNotInColumn
    | .enumerationField values =>
        if values.all column.allowedValues.contains then none else some .enumValuesNotInColumn
    | .otherKind => none

/-- The family's own chain on a field operand, in the Kernel's order.

The table check is the whole story for an A12 document model, and the last arm is doubly guarded:
the column checks run only when the declaration carries table data. -/
def tableEnumChainRefusal (declaration : TableEnumerationDeclaration)
    (parameters : List TableConsistencyParameter) : Option TableEnumRefusal :=
  if !isTableEnumeration declaration then
    some .tableEnumExpected
  else if parameters.length != declaration.dependentColumns.length then
    some .dependentColumnSizeMismatch
  else if parameters.any (· == .otherKind) then
    some .onlyEnumsAllowed
  else if !declaration.tableAvailable then
    none
  else
    (parameters.zip declaration.table).findSome? fun (parameter, column) =>
      parameterValueRefusal parameter column

/-- `ValueNotConsistent`'s static gate: the operand's shape, then the family's chain. -/
def valueNotConsistentRefusal (operand : TableConsistencyOperand)
    (parameters : List TableConsistencyParameter) : Option ValueNotConsistentRefusal :=
  if !operand.isField then
    some .groupOperand
  else if operand.hasWildcard then
    some .wildcardOperand
  else
    (tableEnumChainRefusal operand.declaration parameters).map .family

/-- The mirror check in the ordinary field-value operator: it refuses a table enumeration, where
`ValueNotConsistent` requires one. -/
def fieldValueOperandRefusal (declaration : TableEnumerationDeclaration) : Option TableEnumRefusal :=
  if isTableEnumeration declaration then some .invalidTableEnum else none

/-! ## The whole downstream vocabulary, behind the same constant

Seventeen further catalog classes sit below the declaration gate above, in two stages: the
code-generation table check and the CSV file parser it calls. All of them are reached through one
guard — a model has at least one field whose enumeration declares a table name — and that guard is
the constant this module already owns, re-established here on the **tool-side** interface rather than
inherited from the runtime one.

**The denominator, closed on this carrier.** Two interfaces share the name `IEnumerationType`. The one
the code-generation check reads declares `getTableName()` abstract, and exactly one class in the
checkout implements *that* interface; it returns absence unconditionally. The second interface, from
the model-API package, has no such member at all, so its implementor is not a second answer. Crossing
from the runtime constant to this one is a claim rather than an inheritance, which is why it is
enumerated again here ([`LF116`](../../docs/LEAN-FINDINGS.md)).

**The chain has no branch.** The guard collects the fields whose enumeration declares a table name and
returns success immediately when that list is empty; every downstream method has exactly one caller,
inside that guard. So the seventeen classes are not merely unlikely — no A12 code path reaches the
check that reports them.

Mechanism-derived by exhaustive caller and implementation enumeration over the checkout, not measured:
a table enumeration cannot be authored through any route this project has, so no probe can exercise
the positive branch. This is a statement about that source tree at its reviewed revision.
-/

/-- Where a table-enumeration diagnostic arises. The stages run in this order and each is gated by the
one before, which is why a consumer that reaches none of them reaches none of the classes. -/
inductive TableEnumStage where
  /-- The operand-level checks this module's first half owns. -/
  | declaration
  /-- The code-generation table check: the table must exist and its columns must match the type. -/
  | codegenTableCheck
  /-- The CSV file parser the check above calls on the table's bytes. -/
  | csvLoad
  deriving Repr, DecidableEq

/-- A class reported below the declaration gate. Kept apart from `TableEnumRefusal` because these are
not operand diagnostics: they describe a *file* and a code-generation run, and no operand position
produces them. -/
inductive TableEnumDownstreamRefusal where
  | enumTableMissing
  | tableEnumColumnMissing
  | tableEnumDepColumnMissing
  | tableEnumDiffCategories
  | tableEnumMultilingualDisplayValue
  | tableEnumsNotAllowedForProgrammingLanguage
  | charactersNotAllowed
  | columnNameWrong
  | emptyLine
  | emptyValue
  | enumColumnMissing
  | enumValuesNotUnique
  | numColumnsDontMatch
  | utf8EncodingWrong
  | valueTooLong
  | xmlUiValueNotUnique
  | emptyTable
  deriving Repr, DecidableEq

namespace TableEnumDownstreamRefusal

/-- The exact catalog key. The two stages draw from different catalogs, which is why the prefixes
differ; a consumer assembling a key by prefixing `MVK_` gets every CSV class wrong. -/
def catalogKey : TableEnumDownstreamRefusal → String
  | .enumTableMissing => "MVK_ENUM_TABLE_MISSING"
  | .tableEnumColumnMissing => "MVK_TABLE_ENUM_COLUMN_MISSING"
  | .tableEnumDepColumnMissing => "MVK_TABLE_ENUM_DEP_COLUMN_MISSING"
  | .tableEnumDiffCategories => "MVK_TABLE_ENUM_DIFF_CATEGORIES"
  | .tableEnumMultilingualDisplayValue => "MVK_TABLE_ENUM_WITH_MULTILINGUAL_DISPLAY_VALUE"
  | .tableEnumsNotAllowedForProgrammingLanguage =>
      "MVK_TABLE_ENUMS_NOT_ALLOWED_FOR_PROGRAMMING_LANGUAGE"
  | .charactersNotAllowed => "CHARACTERS_NOT_ALLOWED"
  | .columnNameWrong => "COLUMN_NAME_WRONG"
  | .emptyLine => "EMPTY_LINE"
  | .emptyValue => "EMPTY_VALUE"
  | .enumColumnMissing => "ENUM_COLUMN_MISSING"
  | .enumValuesNotUnique => "ENUM_VALUES_NOT_UNIQUE"
  | .numColumnsDontMatch => "NUM_COLUMNS_DONT_MATCH"
  | .utf8EncodingWrong => "UTF8_ENCODING_WRONG"
  | .valueTooLong => "VALUE_TOO_LONG"
  | .xmlUiValueNotUnique => "XML_UI_VALUE_NOT_UNIQUE"
  | .emptyTable => "EMPTY_TABLE"

/-- Which stage reports the class. -/
def stage : TableEnumDownstreamRefusal → TableEnumStage
  | .enumTableMissing | .tableEnumColumnMissing | .tableEnumDepColumnMissing
  | .tableEnumDiffCategories | .tableEnumMultilingualDisplayValue
  | .tableEnumsNotAllowedForProgrammingLanguage => .codegenTableCheck
  | _ => .csvLoad

/-- Every class of the downstream family. -/
def all : List TableEnumDownstreamRefusal :=
  [.enumTableMissing, .tableEnumColumnMissing, .tableEnumDepColumnMissing,
   .tableEnumDiffCategories, .tableEnumMultilingualDisplayValue,
   .tableEnumsNotAllowedForProgrammingLanguage, .charactersNotAllowed, .columnNameWrong,
   .emptyLine, .emptyValue, .enumColumnMissing, .enumValuesNotUnique, .numColumnsDontMatch,
   .utf8EncodingWrong, .valueTooLong, .xmlUiValueNotUnique, .emptyTable]

end TableEnumDownstreamRefusal

/-- The code-generation guard: the downstream check runs at all only when some field's enumeration
declares a table name. An empty list of such fields returns success before any table is read. -/
def tableEnumCheckRuns (declarations : List TableEnumerationDeclaration) : Bool :=
  declarations.any isTableEnumeration

/-- The classes a model can draw from the downstream stages: all of them when the guard opens, none at
all when it does not. The set is stated rather than a per-class predicate because the guard is
common — nothing distinguishes the classes until it opens. -/
def downstreamRefusals (declarations : List TableEnumerationDeclaration) :
    List TableEnumDownstreamRefusal :=
  if tableEnumCheckRuns declarations then TableEnumDownstreamRefusal.all else []

end A12Kernel
