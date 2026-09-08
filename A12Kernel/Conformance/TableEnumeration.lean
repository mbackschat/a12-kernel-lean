import A12Kernel.Elaboration.TableEnumeration

/-! # Locks on the table-enumeration construct

The cases fix two things a consumer gets wrong in opposite directions: that `ValueNotConsistent` is a condition it might one day see succeed on an A12 model, and — the mirror error — that the four classes behind its first arm are simply dead code rather than a gate that a later model version could open.

The measured witness is the first arm on an ordinary two-value enumeration ([checkpoint](../../docs/SOURCES.md#src-table-enumeration-inertness)). Every case below that exercises a later arm supplies the table declaration by hand, because no A12 model can.
-/

namespace A12Kernel.Conformance.TableEnumeration

open A12Kernel

/-- The measured operand: an ordinary two-value enumeration as an A12 model declares it. -/
private def measuredOperand : TableConsistencyOperand :=
  { declaration := a12TableView ["ALPHA", "BETA"] }

/-- The same enumeration with a table declaration bolted on, which no A12 model produces. It exists
so the later arms are exercised rather than merely stated unreachable. -/
private def tableBacked : TableEnumerationDeclaration :=
  { values := ["ALPHA", "BETA"], tableName := some "T", columnName := some "Key",
    dependentColumns := ["Col"], tableAvailable := true,
    table := [{ name := "Col", allowedValues := ["ALPHA", "BETA"] }] }

/- The measured case, and the constant behind it. The refusal does not depend on the parameter list,
   which is what distinguishes an inert construct from a restricted one. -/
example :
    isTableEnumeration measuredOperand.declaration = false ∧
      valueNotConsistentRefusal measuredOperand [] = some .tableEnumExpected ∧
      valueNotConsistentRefusal measuredOperand [.stringLiteral "ALPHA"] =
        some .tableEnumExpected ∧
      valueNotConsistentRefusal measuredOperand [.otherKind, .otherKind] =
        some .tableEnumExpected := by
  native_decide

/- The A12 declaration drops the table parts whatever the model declares, so the constant is a
   property of the mapping and not of the values. -/
example :
    (a12TableView ["X"]).tableName = none ∧
      (a12TableView ["X"]).dependentColumns = [] ∧
      (a12TableView ["X"]).tableAvailable = false ∧
      (a12TableView ["X"]).values = ["X"] := by
  native_decide

/- Being a table enumeration is the name's presence and nothing else — not the column, not the
   dependent list, not the data. A consumer testing any of the other three gets a different
   predicate, and on the hand-built declaration below a strictly weaker one. -/
example :
    isTableEnumeration { tableName := some "T" } = true ∧
      isTableEnumeration { columnName := some "Key", dependentColumns := ["Col"],
                           tableAvailable := true } = false := by
  native_decide

/- With the first arm cleared, the gate is ordered and each later arm is reachable in turn. The
   parameter-count arm precedes the parameter-kind arm, so a list that is both the wrong length and
   the wrong kind reports its length. -/
example :
    valueNotConsistentRefusal { declaration := tableBacked } [] =
        some .dependentColumnSizeMismatch ∧
      valueNotConsistentRefusal { declaration := tableBacked } [.otherKind, .otherKind] =
        some .dependentColumnSizeMismatch ∧
      valueNotConsistentRefusal { declaration := tableBacked } [.otherKind] =
        some .onlyEnumsAllowed := by
  native_decide

/- The column checks report different classes for a literal and for an enumeration parameter, and
   the enumeration arm asks for containment of the whole declared value set rather than of one
   value — so an enumeration admitting one extra value refuses even though its other values fit. -/
example :
    valueNotConsistentRefusal { declaration := tableBacked } [.stringLiteral "GAMMA"] =
        some .stringValueNotInColumn ∧
      valueNotConsistentRefusal { declaration := tableBacked } [.stringLiteral "ALPHA"] = none ∧
      valueNotConsistentRefusal { declaration := tableBacked }
          [.enumerationField ["ALPHA", "GAMMA"]] = some .enumValuesNotInColumn ∧
      valueNotConsistentRefusal { declaration := tableBacked }
          [.enumerationField ["ALPHA"]] = none := by
  native_decide

/- The column checks are guarded twice over. Absent table data skips them entirely, and so does a
   column the table does not carry — the second is a pass rather than a refusal, which is the arm a
   consumer most plausibly inverts. -/
example :
    valueNotConsistentRefusal
        { declaration := { tableBacked with tableAvailable := false } }
        [.stringLiteral "GAMMA"] = none ∧
      valueNotConsistentRefusal
        { declaration := { tableBacked with
            table := [{ name := "Col", allowedValues := [] }] } }
        [.stringLiteral "GAMMA"] = none := by
  native_decide

/- The mirror class is the same predicate read the other way: the field-value operator refuses
   exactly the declarations `ValueNotConsistent` requires, so in an A12 model it never fires. -/
example :
    fieldValueOperandRefusal (a12TableView ["ALPHA"]) = none ∧
      fieldValueOperandRefusal tableBacked = some .invalidTableEnum := by
  native_decide

/- Six distinct keys, so a consumer subtracting the four it can never see keeps the two it can. -/
example :
    (TableEnumRefusal.all.map (·.catalogKey)).eraseDups.length = 6 ∧
      TableEnumRefusal.all.length = 6 ∧
      TableEnumRefusal.tableEnumExpected.catalogKey = "MVK_TABLE_ENUM_EXPECTED" ∧
      TableEnumRefusal.invalidTableEnum.catalogKey = "MVK_INVALID_TABLE_ENUM" := by
  native_decide

end A12Kernel.Conformance.TableEnumeration
