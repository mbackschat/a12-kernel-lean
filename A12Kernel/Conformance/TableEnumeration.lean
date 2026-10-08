import A12Kernel.Elaboration.TableEnumeration

/-! # Locks on the table-enumeration construct

The cases fix two things a consumer gets wrong in opposite directions: that `ValueNotConsistent` is a condition it might one day see succeed on an A12 model, and — the mirror error — that the four classes behind its table check are simply dead code rather than a gate that a later model version could open.

The measured witnesses are the table check on an ordinary two-value enumeration ([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-table-enumeration-inertness)) and the two shape arms ahead of it ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-gate-raise-points)). Every case below that exercises a later arm supplies the table declaration by hand, because no A12 model can.
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
      valueNotConsistentRefusal measuredOperand [] = some (.family .tableEnumExpected) ∧
      valueNotConsistentRefusal measuredOperand [.stringLiteral "ALPHA"] =
        some (.family .tableEnumExpected) ∧
      valueNotConsistentRefusal measuredOperand [.otherKind, .otherKind] =
        some (.family .tableEnumExpected) := by
  native_decide

/- **The operand's shape is asked first, and answers in the shared classes.** A non-repeating group
   draws `MVK_NO_GROUPS_ALLOWED` and a starred selector `MVK_NO_WILDCARDS_ALLOWED`, each ahead of the
   table check that refuses a field. A gate reading the declaration alone names the family's class
   for both. -/
example :
    (valueNotConsistentRefusal { measuredOperand with isField := false } []).map (·.catalogKey) =
        some "MVK_NO_GROUPS_ALLOWED" ∧
      (valueNotConsistentRefusal { measuredOperand with hasWildcard := true } []).map
        (·.catalogKey) = some "MVK_NO_WILDCARDS_ALLOWED" := by
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

/- With the table check cleared, the chain is ordered and each later arm is reachable in turn. The
   parameter-count arm precedes the parameter-kind arm, so a list that is both the wrong length and
   the wrong kind reports its length. -/
example :
    tableEnumChainRefusal tableBacked [] =
        some .dependentColumnSizeMismatch ∧
      tableEnumChainRefusal tableBacked [.otherKind, .otherKind] =
        some .dependentColumnSizeMismatch ∧
      tableEnumChainRefusal tableBacked [.otherKind] =
        some .onlyEnumsAllowed := by
  native_decide

/- The column checks report different classes for a literal and for an enumeration parameter, and
   the enumeration arm asks for containment of the whole declared value set rather than of one
   value — so an enumeration admitting one extra value refuses even though its other values fit. -/
example :
    tableEnumChainRefusal tableBacked [.stringLiteral "GAMMA"] =
        some .stringValueNotInColumn ∧
      tableEnumChainRefusal tableBacked [.stringLiteral "ALPHA"] = none ∧
      tableEnumChainRefusal tableBacked
          [.enumerationField ["ALPHA", "GAMMA"]] = some .enumValuesNotInColumn ∧
      tableEnumChainRefusal tableBacked
          [.enumerationField ["ALPHA"]] = none := by
  native_decide

/- The column checks are guarded twice over. Absent table data skips them entirely, and so does a
   column the table does not carry — the second is a pass rather than a refusal, which is the arm a
   consumer most plausibly inverts. -/
example :
    tableEnumChainRefusal { tableBacked with tableAvailable := false }
        [.stringLiteral "GAMMA"] = none ∧
      tableEnumChainRefusal { tableBacked with
          table := [{ name := "Col", allowedValues := [] }] }
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

/- **Seventeen downstream classes, one guard.** An A12 model's enumerations open none of it, and a
   declaration carrying a table name opens all of it at once — which is what makes the guard the whole
   content of the family rather than seventeen separate conditions. -/
example :
    downstreamRefusals [a12TableView ["a"], a12TableView []] = [] ∧
      (downstreamRefusals [{ values := ["a"], tableName := some "T" }]).length = 17 := by
  native_decide

/- One table-declaring enumeration among many ordinary ones is enough to open it, so the guard is a
   disjunction over the model rather than a property of the enumeration being checked. -/
example :
    downstreamRefusals
        [a12TableView ["a"], { values := ["b"], tableName := some "T" }, a12TableView ["c"]] =
      TableEnumDownstreamRefusal.all := by
  native_decide

/- The two stages split 6/11 and no downstream class claims the declaration stage, so a consumer can
   route a diagnostic by class alone. The eleven file-parser keys carry no `MVK_` prefix, which is the
   thing a consumer assembling keys mechanically gets wrong. -/
example :
    (TableEnumDownstreamRefusal.all.map (·.catalogKey)).eraseDups.length = 17 ∧
      (TableEnumDownstreamRefusal.all.filter fun r =>
        r.catalogKey.startsWith "MVK_").length = 6 ∧
      TableEnumDownstreamRefusal.emptyTable.stage = .csvLoad ∧
      TableEnumDownstreamRefusal.enumTableMissing.stage = .codegenTableCheck := by
  native_decide

/- The downstream vocabulary is disjoint from the operand vocabulary this module's first half owns:
   no key appears in both, so the two enumerations are not two names for one set. -/
example :
    (TableEnumRefusal.all.map (·.catalogKey)).filter
      (TableEnumDownstreamRefusal.all.map (·.catalogKey)).contains = [] := by
  native_decide

end A12Kernel.Conformance.TableEnumeration
