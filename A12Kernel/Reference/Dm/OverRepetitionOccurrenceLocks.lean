import Lean.Data.Json
import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.OverRepetitionFindings

/-! # Reader-to-finding locks for over-repetition occurrence scope

Each row replays one document of the retained real-Kernel capture
`evidence/kernel-30.8.1/captures/over-repetition-occurrence-scope-2026-10-13/` through the DM
reader and the over-repetition finding API, and compares the three channels the capture observed
under both Kernel strategies ([checkpoint](../../../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope)):
full validation, partial validation under the row's relevance selection, and the computation
operand channel of the model's two computations. The model text below is the retained
`Occ_DM.json` verbatim.

Expected sets name their nodes by the capture's own pointers, resolved against the read model;
findings are compared as sets because no retained observation fixes an emission order.
-/

namespace A12Kernel.Dm.OverRepetitionOccurrenceLocks

open Lean A12Kernel

private def modelText : String := r#"
{
  "header" : {
    "id" : "Occ_DM",
    "modelType" : "document",
    "modelVersion" : "28.4.0",
    "locales" : [ {
      "code" : "en_US"
    } ],
    "labels" : [ ],
    "annotations" : [ ],
    "modelReferences" : [ ]
  },
  "content" : {
    "modelInfo" : {
      "name" : "Occ_DM",
      "variant" : "cockpit",
      "revision" : "Arbeitsversion",
      "immutable" : false
    },
    "modelConfig" : {
      "decimalSeparator" : ".",
      "timeZone" : "Europe/Berlin",
      "conditionLanguage" : {
        "code" : "en_US"
      },
      "fieldRefByShortNameAllowed" : true
    },
    "modelRoot" : {
      "rootGroups" : [ {
        "type" : "Group",
        "id" : "/Occ",
        "name" : "Occ",
        "Group" : {
          "repeatability" : 1,
          "elements" : [ {
            "type" : "Field",
            "id" : "/Occ/Marker",
            "name" : "Marker",
            "Field" : {
              "fieldType" : {
                "type" : "StringType"
              }
            }
          }, {
            "type" : "Field",
            "id" : "/Occ/Total",
            "name" : "Total",
            "Field" : {
              "fieldType" : {
                "type" : "NumberType",
                "NumberType" : {
                  "maxFractionalDigits" : 0
                }
              }
            }
          }, {
            "type" : "Group",
            "id" : "/Occ/Rows",
            "name" : "Rows",
            "Group" : {
              "repeatability" : 2,
              "elements" : [ {
                "type" : "Field",
                "id" : "/Occ/Rows/Qty",
                "name" : "Qty",
                "Field" : {
                  "fieldType" : {
                    "type" : "NumberType",
                    "NumberType" : {
                      "maxFractionalDigits" : 0
                    }
                  }
                }
              }, {
                "type" : "Field",
                "id" : "/Occ/Rows/Unread",
                "name" : "Unread",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  }
                }
              }, {
                "type" : "Group",
                "id" : "/Occ/Rows/Detail",
                "name" : "Detail",
                "Group" : {
                  "repeatability" : 1,
                  "elements" : [ {
                    "type" : "Field",
                    "id" : "/Occ/Rows/Detail/Qty2",
                    "name" : "Qty2",
                    "Field" : {
                      "fieldType" : {
                        "type" : "NumberType",
                        "NumberType" : {
                          "maxFractionalDigits" : 0
                        }
                      }
                    }
                  } ]
                }
              } ]
            }
          }, {
            "type" : "Group",
            "id" : "/Occ/Notes",
            "name" : "Notes",
            "Group" : {
              "repeatability" : 5,
              "elements" : [ {
                "type" : "Field",
                "id" : "/Occ/Notes/Memo",
                "name" : "Memo",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  }
                }
              } ]
            }
          }, {
            "type" : "Group",
            "id" : "/Occ/Wide",
            "name" : "Wide",
            "Group" : {
              "repeatability" : 5,
              "elements" : [ {
                "type" : "Group",
                "id" : "/Occ/Wide/Fix",
                "name" : "Fix",
                "Group" : {
                  "repeatability" : 1,
                  "elements" : [ {
                    "type" : "Field",
                    "id" : "/Occ/Wide/Fix/Calc",
                    "name" : "Calc",
                    "Field" : {
                      "fieldType" : {
                        "type" : "NumberType",
                        "NumberType" : {
                          "maxFractionalDigits" : 0
                        }
                      }
                    }
                  }, {
                    "type" : "Computation",
                    "id" : "/Occ/Wide/Fix/CalcComp",
                    "name" : "CalcComp",
                    "Computation" : {
                      "computedFieldRelPath" : "../Calc",
                      "computationAlternatives" : [ {
                        "operation" : "1"
                      } ],
                      "errorMessage" : [ {
                        "locale" : "en_US",
                        "text" : "Probe"
                      } ]
                    }
                  } ]
                }
              } ]
            }
          }, {
            "type" : "Computation",
            "id" : "/Occ/TotalComp",
            "name" : "TotalComp",
            "Computation" : {
              "computedFieldRelPath" : "../Total",
              "computationAlternatives" : [ {
                "operation" : "Sum(Rows*/Detail/Qty2)"
              } ],
              "errorMessage" : [ {
                "locale" : "en_US",
                "text" : "Probe"
              } ]
            }
          } ]
        }
      } ]
    }
  }
}"#

private def world : World := { now := { epochMillis := 0 } }

private def model? : Option DmModel := do
  let dm ← (readModel (← (Json.parse modelText).toOption)).toOption
  if !dm.refusals.isEmpty then none
  pure dm

/-- The model reads with no refusal and keeps both computations, so every row below measures the
finding API rather than a silently thinned model. -/
example : (model?.map fun dm => dm.computations.length) = some 2 := by native_decide

/-- A capture pointer: the repeatable row, the nonrepeatable group instance beneath it, or a field
of it, each at its single enclosing row index. Every node of this model has exactly one coordinate. -/
private inductive Pointer where
  | row (group : GroupPath) (index : Nat)
  | group (group : GroupPath) (index : Nat)
  | cell (group : GroupPath) (name : String) (index : Nat)

private def resolve (dm : DmModel) : Pointer → Option OverRepetitionNode
  | .row group index => do
      let declared ← dm.flat.repeatableGroups.find? (·.path == group)
      pure (.row { group := declared.level, path := [index] })
  | .group group index => pure (.group { path := group, coordinates := [index] })
  | .cell group name index => do
      let field ← dm.flat.fields.find? fun field => field.groupPath == group && field.name == name
      pure (.cell { field := field.id, path := [index] })

private abbrev Expected := List (OverRepetitionCode × Pointer)

private def rows : GroupPath := ["Occ", "Rows"]
private def detail : GroupPath := ["Occ", "Rows", "Detail"]
private def wide : GroupPath := ["Occ", "Wide"]
private def fix : GroupPath := ["Occ", "Wide", "Fix"]

private def zeile (group : GroupPath) (index : Nat) : OverRepetitionCode × Pointer :=
  (.rowNumberTooLarge, .row group index)
private def kontextGroup (group : GroupPath) (index : Nat) : OverRepetitionCode × Pointer :=
  (.contextNumberTooLarge, .group group index)
private def kontextCell (group : GroupPath) (name : String) (index : Nat) :
    OverRepetitionCode × Pointer :=
  (.contextNumberTooLarge, .cell group name index)

private def expectedFindings (dm : DmModel) (expected : Expected) :
    Option (List OverRepetitionFinding) :=
  expected.mapM fun (code, pointer) => (resolve dm pointer).map ({ code, node := · })

/-- Whether two finding lists hold the same duplicate-free set of nodes. -/
private def sameSet (actual expected : List OverRepetitionFinding) : Bool :=
  actual.eraseDups.length == actual.length && expected.eraseDups.length == expected.length &&
    actual.length == expected.length && actual.all expected.contains && expected.all actual.contains

private def selected (path : GroupPath) : ValidationRelevanceScope :=
  .partialSet [RelevantEntityPattern.allInstances path]

/-- One retained document with its relevance selection and the three observed finding sets. -/
private structure Row where
  document : Json
  scope : ValidationRelevanceScope := selected ["Occ"]
  full : Expected
  partialSet : Expected
  compute : Expected

private def rowsFrom (tail : List Json) : (String × Json) :=
  ("Rows", Json.arr (Json.mkObj [("Detail", Json.mkObj [("Qty2", Json.str "5")])] :: tail).toArray)

private def document (rowTail : List Json) (members : List (String × Json) := []) : Json :=
  Json.mkObj [("Occ", Json.mkObj ([("Marker", Json.str "ready"), rowsFrom rowTail] ++ members))]

private def emptyRow : Json := Json.mkObj []
private def detailRow (qty2 : Json) : Json := Json.mkObj [("Detail", Json.mkObj [("Qty2", qty2)])]

/-- The three channels one document draws: full validation, partial validation under the row's
scope, and the computation channel of the plan whose operand is `Qty2` and whose targets are
`Total` and `Calc`. -/
private def observed (row : Row) (dm : DmModel) :
    Option (List OverRepetitionFinding × List OverRepetitionFinding × List OverRepetitionFinding) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let raw ← (readDocument dm row.document).toOption
  if !raw.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let field (group : GroupPath) (name : String) :=
    dm.flat.fields.find? fun field => field.groupPath == group && field.name == name
  let qty2 ← field detail "Qty2"
  let total ← field ["Occ"] "Total"
  let target ← field fix "Calc"
  let plan ← (checkImplicitGuardFormalInputPlan dm.flat [qty2.id] [total.id, target.id]).toOption
  pure (checked.overRepetitionFindings, checked.overRepetitionFindingsUnder row.scope,
    plan.structuralFindings checked)

private def holds (row : Row) : Bool :=
  match model? with
  | none => false
  | some dm =>
      match observed row dm, expectedFindings dm row.full, expectedFindings dm row.partialSet,
          expectedFindings dm row.compute with
      | some (full, partialSet, compute), some expectedFull, some expectedPartial,
          some expectedCompute =>
          sameSet full expectedFull && sameSet partialSet expectedPartial &&
            sameSet compute expectedCompute
      | _, _, _, _ => false

private def detailEmpty : Json := Json.mkObj [("Detail", Json.mkObj [])]

private def nullSiblings : Json :=
  Json.mkObj [("Detail", Json.mkObj [("Qty2", Json.null)]), ("Qty", Json.null), ("Unread", Json.str "")]

private def notes : (String × Json) :=
  ("Notes", Json.arr #[emptyRow, emptyRow, Json.mkObj [("Memo", Json.str "x")]])

private def fixEmpty : Json := Json.mkObj [("Fix", Json.mkObj [])]

/-- Control: every row within its cap, so the document draws nothing in any channel. -/
private def control : Row where
  document := document [detailEmpty] [notes, ("Wide", Json.arr #[fixEmpty])]
  full := []
  partialSet := []
  compute := []

example : holds control = true := by native_decide

/-- An empty nonrepeatable group instance beneath the over-capacity row draws its own context
finding. The Kernel lists it although the group holds nothing, so a cell-only account misses it. -/
private def fixedGroupEmpty : Row where
  document := document [emptyRow, detailEmpty]
  full := [zeile rows 3, kontextGroup detail 3]
  partialSet := [zeile rows 3, kontextGroup detail 3]
  compute := [zeile rows 3, kontextGroup detail 3]

example : holds fixedGroupEmpty = true := by native_decide

/-- Present-empty siblings are written nodes, so each draws a finding in validation. The
computation channel retains only the operand `Qty2` and the ancestor groups of operand and computed
fields, so `Qty` and `Unread` (neither an operand nor an ancestor) drop out while `Detail` stays. A
comparable-group-path scope would also keep the siblings. -/
private def nullSiblingsFull : Expected :=
  [zeile rows 3, kontextGroup detail 3, kontextCell detail "Qty2" 3,
   kontextCell rows "Qty" 3, kontextCell rows "Unread" 3]

private def nullSiblingsCompute : Expected :=
  [zeile rows 3, kontextGroup detail 3, kontextCell detail "Qty2" 3]

private def nullSiblingsDocument : Json := document [emptyRow, nullSiblings]

private def fixedGroupNullSiblings : Row where
  document := nullSiblingsDocument
  full := nullSiblingsFull
  partialSet := nullSiblingsFull
  compute := nullSiblingsCompute

example : holds fixedGroupNullSiblings = true := by native_decide

/-- The index check runs before relevance is consulted: an empty selection ends the call before any
check, while every nonempty selection reports the whole set, including selections naming only
entities that carry no finding (`Marker`) or that lie outside the over-capacity row (`Memo`). A
relevance-filtered account would report the empty set or a subset in those two rows. -/
private def emptySelection : Row where
  document := nullSiblingsDocument
  scope := .partialSet []
  full := nullSiblingsFull
  partialSet := []
  compute := nullSiblingsCompute

private def markerSelection : Row where
  document := nullSiblingsDocument
  scope := selected ["Occ", "Marker"]
  full := nullSiblingsFull
  partialSet := nullSiblingsFull
  compute := nullSiblingsCompute

private def memoSelection : Row where
  document := nullSiblingsDocument
  scope := selected ["Occ", "Notes", "Memo"]
  full := nullSiblingsFull
  partialSet := nullSiblingsFull
  compute := nullSiblingsCompute

example : holds emptySelection = true := by native_decide
example : holds markerSelection = true := by native_decide
example : holds memoSelection = true := by native_decide

/-- A malformed over-limit operand draws only the structural findings. The retained row reports no
Number-format finding in any channel: over-repetition replaces the cell's formal cause, which the
example after this row asserts on the read cell. -/
private def malformedOperand : Row where
  document := document [emptyRow, detailRow (Json.str "bad")]
  full := [zeile rows 3, kontextGroup detail 3, kontextCell detail "Qty2" 3]
  partialSet := [zeile rows 3, kontextGroup detail 3, kontextCell detail "Qty2" 3]
  compute := [zeile rows 3, kontextGroup detail 3, kontextCell detail "Qty2" 3]

example : holds malformedOperand = true := by native_decide

example : (model?.bind fun dm => do
    let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
    let raw ← (readDocument dm malformedOperand.document).toOption
    let checked ← (checkDocument prepared "en_US" raw.data).toOption
    let qty2 ← dm.flat.fields.find? fun field => field.groupPath == detail && field.name == "Qty2"
    (checked.read { field := qty2.id, path := [3] }).toOption.map (·.findings)) =
    some [.overRepetition] := by
  native_decide

/-- A sibling repeatable group whose own row 3 is within capacity shares the over-capacity row's
leading coordinate. `Notes[3]` holds a written cell and draws nothing, which kills a
coordinate-prefix containment account (that would stamp it as a context finding). -/
private def siblingCoordinateTwin : Row where
  document := document [emptyRow, emptyRow] [notes]
  full := [zeile rows 3]
  partialSet := [zeile rows 3]
  compute := [zeile rows 3]

example : holds siblingCoordinateTwin = true := by native_decide

/-- The twin repeats beneath a nonrepeatable group: `Wide[3]/Fix` sits at the violated row's
coordinate yet inside a different repeatable ancestry, so it too draws nothing. -/
private def siblingCoordinateTwinNested : Row where
  document := document [emptyRow, emptyRow] [notes, ("Wide", Json.arr #[emptyRow, emptyRow, fixEmpty])]
  full := [zeile rows 3]
  partialSet := [zeile rows 3]
  compute := [zeile rows 3]

example : holds siblingCoordinateTwinNested = true := by native_decide

private def sixWide (last : Json) : (String × Json) :=
  ("Wide", Json.arr #[emptyRow, emptyRow, emptyRow, emptyRow, emptyRow, last])

/-- The computed target `Calc` is no operand, so the computation channel drops its own cell yet keeps
`Wide[6]` and `Wide[6]/Fix`, the target's ancestor groups. An operand-only ancestry account would
drop all three. Validation reports the cell as well. -/
private def targetAncestryOverLimit : Row where
  document := document [] [sixWide (Json.mkObj [("Fix", Json.mkObj [("Calc", Json.null)])])]
  full := [zeile wide 6, kontextGroup fix 6, kontextCell fix "Calc" 6]
  partialSet := [zeile wide 6, kontextGroup fix 6, kontextCell fix "Calc" 6]
  compute := [zeile wide 6, kontextGroup fix 6]

example : holds targetAncestryOverLimit = true := by native_decide

/-- Without a written `Calc` the three channels agree: the ancestor group instance alone follows the
row. -/
private def targetAncestryOverLimitEmptyFix : Row where
  document := document [] [sixWide fixEmpty]
  full := [zeile wide 6, kontextGroup fix 6]
  partialSet := [zeile wide 6, kontextGroup fix 6]
  compute := [zeile wide 6, kontextGroup fix 6]

example : holds targetAncestryOverLimitEmptyFix = true := by native_decide

end A12Kernel.Dm.OverRepetitionOccurrenceLocks
