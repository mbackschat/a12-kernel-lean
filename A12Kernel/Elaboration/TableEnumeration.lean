/-! # `ValueNotConsistent` and the table enumeration it needs, which an A12 document model never has

A **table enumeration** is an enumeration whose values live in an external data table rather than in the model: the declaration names a table, a key column, and a list of *dependent* columns. The `ValueNotConsistent` condition exists for it and for nothing else — it asks whether a field's value is inconsistent with the values of the columns its table declares as dependent, so the whole construct is meaningless for an enumeration whose values are written out in the model.

**The load-bearing fact is a constant.** An A12 document model's enumeration declaration reports no table name, no column name, and no dependent columns, whatever the model says; the Kernel's table-enumeration predicate is exactly "a table name is present". So in an A12 model no enumeration is a table enumeration, and the construct's *first* check refuses every candidate. `ValueNotConsistent` parses, elaborates, and is then rejected — always, on any operand, in any model of this kind.

That single constant decides the whole family, so the classes below split into one a consumer will meet and four it will not:

1. **The operand must be a field, carry no wildcard, and be a table enumeration.** The third arm is the one that fires, and it is measured.
2. **The parameter count must equal the declared dependent-column count.** Unreachable behind arm 1; and the declared count is itself always zero here.
3. **Each parameter must be an enumeration.** Unreachable behind arm 1.
4. **Each parameter's value must appear in its dependent column** — one class for a string literal, another for an enumeration whose value set is not contained in the column's. Unreachable behind arm 1, and additionally behind a second constant: the check runs only when the declaration carries *table data*, which no A12 declaration does either.

A fifth class belongs to the same constant from the other side. The ordinary field-value operator refuses a table enumeration outright, so `invalidTableEnum` is the mirror of `tableEnumExpected`: one fires when an operand is not a table enumeration and the other when it is, and in an A12 model the first always fires and the second never can.

**Why model a construct that cannot succeed.** A consumer enumerating the catalogs meets all six keys and cannot tell from the catalog which it will ever see. An importer reading a model that came from elsewhere needs to know that a `ValueNotConsistent` rule is not a rule it failed to understand but one the Kernel itself rejects. And the constant is a *version* fact about the A12 mapping, not a law of the language: the accessor's own neighbours in the Kernel's tool API are not constant, so a later model version could make four of these live without any change to the condition's semantics. Recording the gate in full is what makes that change cheap to absorb.

**Evidence.** `tableEnumExpected` is measured on an ordinary two-value enumeration ([checkpoint](../../docs/SOURCES.md#src-table-enumeration-inertness)). The other four rest on the constant, established by enumerating every implementation of the table-name accessor reachable from an A12 document model — there is exactly one, and it returns absence unconditionally. That is a mechanism claim discharged by exhaustive implementation search, not a measured one, and it is marked as such in the coverage record.

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
data is unavailable and still pass the first arm. -/
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
  isField : Bool := true
  hasWildcard : Bool := false
  declaration : TableEnumerationDeclaration
  deriving Repr, DecidableEq

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

/-- `ValueNotConsistent`'s static gate, in the Kernel's order.

The first arm is the whole story for an A12 document model, and the last is doubly guarded: the
column checks run only when the declaration carries table data. -/
def valueNotConsistentRefusal (operand : TableConsistencyOperand)
    (parameters : List TableConsistencyParameter) : Option TableEnumRefusal :=
  if !isTableEnumeration operand.declaration then
    some .tableEnumExpected
  else if parameters.length != operand.declaration.dependentColumns.length then
    some .dependentColumnSizeMismatch
  else if parameters.any (· == .otherKind) then
    some .onlyEnumsAllowed
  else if !operand.declaration.tableAvailable then
    none
  else
    (parameters.zip operand.declaration.table).findSome? fun (parameter, column) =>
      parameterValueRefusal parameter column

/-- The mirror check in the ordinary field-value operator: it refuses a table enumeration, where
`ValueNotConsistent` requires one. -/
def fieldValueOperandRefusal (declaration : TableEnumerationDeclaration) : Option TableEnumRefusal :=
  if isTableEnumeration declaration then some .invalidTableEnum else none

end A12Kernel
