import Lean.Data.Json
import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Reader-to-finding locks for generated requiredness

Each row replays one document of the retained real-Kernel capture
`evidence/kernel-30.8.1/captures/generated-requiredness-2026-10-13/` through the DM reader and the
generated-requiredness evaluator, and compares the `mandatoryField` addresses the capture observed under
both Kernel strategies ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-generated-requiredness-k14)):
full validation, and the partial call under the row's relevance selection. The model text below is the
retained `Req_DM.json` verbatim; documents and selections are the retained `request.json` rows.

Expected sets name their cells by the capture's own pointers, resolved against the read model, with the
elided first repetition written as row 1. Each fired address is an ERROR of type OMISSION whose error and
fill-to-fix pointers are the address itself, which the evaluator's `mandatoryAddresses` projection
presupposes; sets are compared as sets because no retained observation fixes an emission order.
-/

namespace A12Kernel.Dm.GeneratedRequirednessLocks

open Lean A12Kernel

private def modelText : String := r#"
{
  "header" : {
    "id" : "Req_DM",
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
      "name" : "Req_DM",
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
        "id" : "/Req",
        "name" : "Req",
        "Group" : {
          "repeatability" : 1,
          "elements" : [ {
            "type" : "Field",
            "id" : "/Req/AbsNum",
            "name" : "AbsNum",
            "Field" : {
              "fieldType" : {
                "type" : "NumberType",
                "NumberType" : {
                  "maxFractionalDigits" : 0
                }
              },
              "requirednessConfig" : {
                "mode" : "absoluteOrRelativeToNextRepAncestor"
              }
            }
          }, {
            "type" : "Field",
            "id" : "/Req/Marker",
            "name" : "Marker",
            "Field" : {
              "fieldType" : {
                "type" : "StringType"
              }
            }
          }, {
            "type" : "Group",
            "id" : "/Req/Ship",
            "name" : "Ship",
            "Group" : {
              "repeatability" : 1,
              "elements" : [ {
                "type" : "Field",
                "id" : "/Req/Ship/City",
                "name" : "City",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  }
                }
              }, {
                "type" : "Field",
                "id" : "/Req/Ship/Zip",
                "name" : "Zip",
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
                "id" : "/Req/Ship/Street",
                "name" : "Street",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  },
                  "requirednessConfig" : {
                    "mode" : "relativeToParent"
                  }
                }
              }, {
                "type" : "Field",
                "id" : "/Req/Ship/AbsInShip",
                "name" : "AbsInShip",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  },
                  "requirednessConfig" : {
                    "mode" : "absoluteOrRelativeToNextRepAncestor"
                  }
                }
              }, {
                "type" : "Rule",
                "id" : "/Req/Ship/ChkStreet",
                "name" : "ChkStreet",
                "Rule" : {
                  "errorEntityRelPath" : "../Street",
                  "errorCode" : "ChkStreet",
                  "errorCondition" : "FieldNotFilled(Street)",
                  "severity" : "ERROR",
                  "errorMessage" : [ {
                    "locale" : "en_US",
                    "text" : "Probe"
                  } ]
                }
              } ]
            }
          }, {
            "type" : "Group",
            "id" : "/Req/Items",
            "name" : "Items",
            "Group" : {
              "repeatability" : 3,
              "elements" : [ {
                "type" : "Field",
                "id" : "/Req/Items/Qty",
                "name" : "Qty",
                "Field" : {
                  "fieldType" : {
                    "type" : "NumberType",
                    "NumberType" : {
                      "maxFractionalDigits" : 0
                    }
                  },
                  "requirednessConfig" : {
                    "mode" : "absoluteOrRelativeToNextRepAncestor"
                  }
                }
              }, {
                "type" : "Field",
                "id" : "/Req/Items/Note",
                "name" : "Note",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  }
                }
              }, {
                "type" : "Group",
                "id" : "/Req/Items/Pack",
                "name" : "Pack",
                "Group" : {
                  "repeatability" : 1,
                  "elements" : [ {
                    "type" : "Field",
                    "id" : "/Req/Items/Pack/Size",
                    "name" : "Size",
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
                    "id" : "/Req/Items/Pack/Label",
                    "name" : "Label",
                    "Field" : {
                      "fieldType" : {
                        "type" : "StringType"
                      },
                      "requirednessConfig" : {
                        "mode" : "relativeToParent"
                      }
                    }
                  }, {
                    "type" : "Field",
                    "id" : "/Req/Items/Pack/Code",
                    "name" : "Code",
                    "Field" : {
                      "fieldType" : {
                        "type" : "StringType"
                      },
                      "requirednessConfig" : {
                        "mode" : "absoluteOrRelativeToNextRepAncestor"
                      }
                    }
                  } ]
                }
              }, {
                "type" : "Rule",
                "id" : "/Req/Items/ChkQty",
                "name" : "ChkQty",
                "Rule" : {
                  "errorEntityRelPath" : "../Qty",
                  "errorCode" : "ChkQty",
                  "errorCondition" : "[Qty] < 100",
                  "severity" : "ERROR",
                  "errorMessage" : [ {
                    "locale" : "en_US",
                    "text" : "Probe"
                  } ]
                }
              } ]
            }
          }, {
            "type" : "Group",
            "id" : "/Req/Box",
            "name" : "Box",
            "Group" : {
              "repeatability" : 1,
              "elements" : [ {
                "type" : "Field",
                "id" : "/Req/Box/Tag",
                "name" : "Tag",
                "Field" : {
                  "fieldType" : {
                    "type" : "StringType"
                  },
                  "requirednessConfig" : {
                    "mode" : "relativeToParent"
                  }
                }
              }, {
                "type" : "Group",
                "id" : "/Req/Box/Lines",
                "name" : "Lines",
                "Group" : {
                  "repeatability" : 2,
                  "elements" : [ {
                    "type" : "Field",
                    "id" : "/Req/Box/Lines/Val",
                    "name" : "Val",
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
            "type" : "Rule",
            "id" : "/Req/ChkAbs",
            "name" : "ChkAbs",
            "Rule" : {
              "errorEntityRelPath" : "../AbsNum",
              "errorCode" : "ChkAbs",
              "errorCondition" : "[AbsNum] < 100",
              "severity" : "ERROR",
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

/-- The model reads with no refusal and keeps all seven required declarations, so every row below measures
the generated mechanism rather than a silently thinned model. -/
example : (model?.map fun dm => (dm.flat.fields.filter (·.requiredness.isSome)).length) = some 7 := by
  native_decide

/-- A capture pointer: the field's group path and name, and the repeatable-row coordinates of its cell. -/
private structure Target where
  group : GroupPath
  name : String
  path : List Nat := []

private def resolve (dm : DmModel) (target : Target) : Option CellAddr := do
  let field ← dm.flat.fields.find? fun field =>
    field.groupPath == target.group && field.name == target.name
  pure { field := field.id, path := target.path }

private abbrev Expected := List Target

private def absNum : Target := { group := ["Req"], name := "AbsNum" }
private def absInShip : Target := { group := ["Req", "Ship"], name := "AbsInShip" }
private def street : Target := { group := ["Req", "Ship"], name := "Street" }
private def tag : Target := { group := ["Req", "Box"], name := "Tag" }
private def qty (row : Nat) : Target := { group := ["Req", "Items"], name := "Qty", path := [row] }
private def label (row : Nat) : Target :=
  { group := ["Req", "Items", "Pack"], name := "Label", path := [row] }
private def code (row : Nat) : Target :=
  { group := ["Req", "Items", "Pack"], name := "Code", path := [row] }

private def expectedAddresses (dm : DmModel) (expected : Expected) : Option (List CellAddr) :=
  expected.mapM (resolve dm)

/-- Whether two address lists hold the same duplicate-free set. -/
private def sameSet (actual expected : List CellAddr) : Bool :=
  actual.eraseDups.length == actual.length && expected.eraseDups.length == expected.length &&
    actual.length == expected.length && actual.all expected.contains && expected.all actual.contains

/-- One retained document with its relevance selection (the request's `relevant` paths, each selected at
every instance) and the observed `mandatoryField` sets of full and partial validation. A partial set
equal to the full set is the default. -/
private structure Row where
  document : String
  relevant : List GroupPath := [["Req"]]
  full : Expected
  partialSet : Expected := full

/-- The generated `mandatoryField` addresses of full validation and of the partial call. -/
private def observed (row : Row) (dm : DmModel) : Option (List CellAddr × List CellAddr) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let raw ← (readDocument dm (← (Json.parse row.document).toOption)).toOption
  if !raw.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let full ← checked.fullRequiredEvaluations.toOption
  let view ← (checked.applyPartialGeneratedPreliminaryForScope
    (.partialSet (row.relevant.map RelevantEntityPattern.allInstances))).toOption
  pure (RequiredEvaluation.mandatoryAddresses full,
    RequiredEvaluation.mandatoryAddresses view.required)

private def holds (row : Row) : Bool :=
  match model? with
  | none => false
  | some dm =>
      match observed row dm, expectedAddresses dm row.full, expectedAddresses dm row.partialSet with
      | some (full, partialSet), some expectedFull, some expectedPartial =>
          sameSet full expectedFull && sameSet partialSet expectedPartial
      | _, _, _ => false

/-- Both absolute fields draw, `AbsInShip` included although `Ship` is uninstantiated. Kills an account that
evaluates requirements of instantiated groups only. -/
private def emptyDocument : Row where
  document := r#"{"Req":{}}"#
  full := [absNum, absInShip]

example : holds emptyDocument = true := by native_decide

/-- Control: filled absolute fields draw nothing, and `AbsInShip` alone fills `Ship`, so `Street` draws. -/
private def absFilledControl : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"}}}"#
  full := [street]

example : holds absFilledControl = true := by native_decide

/-- Control: an admitted `City` is parent content, so `Street` draws. -/
private def shipAdmittedSibling : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"City":"x","AbsInShip":"a"}}}"#
  full := [street]

example : holds shipAdmittedSibling = true := by native_decide

/-- A malformed `Zip` is not admitted content, so `Street` stays silent. Kills raw placement counted as
parent content. -/
private def shipMalformedOnlySibling : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"Zip":"bad"}}}"#
  full := [absInShip]

example : holds shipMalformedOnlySibling = true := by native_decide

/-- An empty `Ship` object holds no content, so `Street` stays silent. Kills the empty object as content. -/
private def shipEmptyObject : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{}}}"#
  full := [absInShip]

example : holds shipEmptyObject = true := by native_decide

/-- An instantiated empty row draws `Qty` and `Code` (the nearest repeatable ancestor gates both) but not
`Label`, whose parent `Pack` holds nothing. -/
private def itemsEmptyRow : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{}]}}"#
  full := [code 1, qty 1, street]

example : holds itemsEmptyRow = true := by native_decide

/-- An admitted `Size` fills `Pack`, so `Label` joins `Code`; the filled `Qty` draws nothing. -/
private def itemsPackAdmitted : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{"Qty":"5","Pack":{"Size":"1"}}]}}"#
  full := [code 1, label 1, street]

example : holds itemsPackAdmitted = true := by native_decide

/-- Control: a fully filled row draws nothing. -/
private def itemsPackFilledControl : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{"Qty":"5","Pack":{"Size":"1","Label":"l","Code":"c"}}]}}"#
  full := [street]

example : holds itemsPackFilledControl = true := by native_decide

/-- The fourth row exceeds capacity and draws nothing, although the empty in-capacity row of `itemsEmptyRow`
draws `Qty` and `Code`. Kills over-capacity rows being evaluated. -/
private def itemsOverLimit : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{"Qty":"1","Pack":{"Code":"c"}},{"Qty":"2","Pack":{"Code":"c"}},{"Qty":"3","Pack":{"Code":"c"}},{}]}}"#
  full := [label 1, label 2, label 3, street]

example : holds itemsOverLimit = true := by native_decide

/-- An instantiated empty `Lines` row already fills `Box`, so `Tag` draws. Kills the account where only
valued descendants count as parent content. -/
private def boxEmptyChildRow : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Box":{"Lines":[{}]}}}"#
  full := [tag, street]

example : holds boxEmptyChildRow = true := by native_decide

/-- Relevance is per field: the same row's `Code` and `Street` lie outside the selection and draw nothing. -/
private def itemsPartialQty : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{}]}}"#
  relevant := [["Req", "Items", "Qty"]]
  full := [code 1, qty 1, street]
  partialSet := [qty 1]

example : holds itemsPartialQty = true := by native_decide

/-- `Marker` covers no required field. Kills generated rules running outside the selection. -/
private def itemsPartialMarker : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{}]}}"#
  relevant := [["Req", "Marker"]]
  full := [code 1, qty 1, street]
  partialSet := []

example : holds itemsPartialMarker = true := by native_decide

/-- An empty selection evaluates no generated rule. Kills an empty selection read as full validation. -/
private def itemsPartialEmpty : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"AbsInShip":"a"},"Items":[{}]}}"#
  relevant := []
  full := [code 1, qty 1, street]
  partialSet := []

example : holds itemsPartialEmpty = true := by native_decide

/-- `City` is admitted but outside the selection, so the parent gate is not filled and `Street` is not
required here although full validation requires it. Kills a gate ignoring partial relevance. -/
private def shipPartialStreetOnly : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"City":"x","AbsInShip":"a"}}}"#
  relevant := [["Req", "Ship", "Street"]]
  full := [street]
  partialSet := []

example : holds shipPartialStreetOnly = true := by native_decide

/-- Selecting the group covers `Street` and the admitted `City`, restoring the requirement. -/
private def shipPartialShip : Row where
  document := r#"{"Req":{"Marker":"m","AbsNum":"5","Ship":{"City":"x","AbsInShip":"a"}}}"#
  relevant := [["Req", "Ship"]]
  full := [street]

example : holds shipPartialShip = true := by native_decide

/-- The selection keeps `AbsNum`; `AbsInShip` lies outside it. -/
private def emptyPartialAbsnum : Row where
  document := r#"{"Req":{}}"#
  relevant := [["Req", "AbsNum"]]
  full := [absNum, absInShip]
  partialSet := [absNum]

example : holds emptyPartialAbsnum = true := by native_decide

/-- No required field is selected. -/
private def emptyPartialMarker : Row where
  document := r#"{"Req":{}}"#
  relevant := [["Req", "Marker"]]
  full := [absNum, absInShip]
  partialSet := []

example : holds emptyPartialMarker = true := by native_decide

/-- The authored messages full validation reports, each `code pointer`, from every authored rule run
on `fullValidationDocument`. -/
private def fullAuthored (document : String) : Option (List String) := do
  let dm ← model?
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let raw ← (readDocument dm (← (Json.parse document).toOption)).toOption
  if !raw.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let messages ← dm.rules.flatMapM fun rule => do
    let plan ← (checkValidationRule dm .english rule).toOption
    (runValidationRule world validated plan).toOption
  pure ((messages.map fun message =>
    let observed := observe dm.flat message
    s!"{observed.code} {observed.pointer}").mergeSort (compare · · != .gt))

/- Authored rules read a required-empty cell as formally unavailable: `FieldNotFilled(Street)` fires
   only while `Street` draws no generated finding, and `[AbsNum] < 100` only once `AbsNum` is filled.
   The retained full-validation messages of `empty-document` and `abs-filled-control`. -/
example :
    fullAuthored emptyDocument.document = some ["ChkStreet Req/Ship/Street"] ∧
    fullAuthored absFilledControl.document = some ["ChkAbs Req/AbsNum", "ChkQty Req/Items/Qty",
      "ChkQty Req/Items[2]/Qty", "ChkQty Req/Items[3]/Qty"] := by
  native_decide

end A12Kernel.Dm.GeneratedRequirednessLocks
