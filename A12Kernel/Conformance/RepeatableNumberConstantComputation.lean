import A12Kernel.Elaboration.RepeatableNumberConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Repeatable ordinary Number constant locks

The Kernel rows behind these cases are the [cross-group carrier](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)
and the [target-check](../../docs/SOURCES.md#src-repeatable-number-constant-target-check) checkpoints.
-/

namespace A12Kernel.Conformance.RepeatableNumberConstantComputation

open A12Kernel

private def whole : FlatFieldDecl := {
  id := 1
  groupPath := ["Probe", "Tasks"]
  name := "Whole"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def cents : FlatFieldDecl := {
  id := 2
  groupPath := ["Probe", "Tasks"]
  name := "Cents"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

/-- Only the measured bound is declared. The Kernel row behind these cases errored an over-maximum
constant; no under-minimum row was observed, so this fixture asserts none. -/
private def bounded : FlatFieldDecl := {
  id := 3
  groupPath := ["Probe", "Tasks"]
  name := "Bounded"
  policy := { kind := .number { scale := 0, signed := true } }
  numericTargetConstraints := { maximum := some 10 }
  repeatableScope := [10]
}

/-- A target that *requires* two fractional digits, so the store's padding half has something to do
that the `maxFractionalDigits`-only targets above cannot show. -/
private def padded : FlatFieldDecl := {
  id := 5
  groupPath := ["Probe", "Tasks"]
  name := "Padded"
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }
  repeatableScope := [10]
}

private def note : FlatFieldDecl := {
  id := 4
  groupPath := ["Probe", "Store"]
  name := "Note"
  policy := { kind := .number { scale := 0, signed := true } }
}

private def model : FlatModel := {
  fields := [whole, cents, bounded, padded, note]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Tasks"], repeatability := some 3 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

private def outcomes? (declaringGroup : GroupPath) (target : FieldId)
    (constant : StoredNumber) (count : Nat) :
    Option (List RepeatableNumberConstantComputationOutcome) :=
  (checkRepeatableNumberConstantComputation model declaringGroup target
      constant).toOption.bind fun operation =>
    (rows count).bind fun input => (operation.execute input).toOption

private def kernelCode? (declaringGroup : GroupPath) (target : FieldId)
    (constant : StoredNumber) : Option String :=
  match checkRepeatableNumberConstantComputation model declaringGroup target constant with
  | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
  | .ok _ => none

/- The constant reaches every physical target row and no more, from an ancestor exactly as from the
target's own group. A negative constant is ordinary on a signed target. Two rows, two outcomes; no
rows, none at all rather than one implicit instance. -/
example : (outcomes? ["Probe"] whole.id { unscaled := -1, scale := 0 } 2,
    outcomes? ["Probe", "Tasks"] whole.id { unscaled := -1, scale := 0 } 2,
    outcomes? ["Probe"] whole.id { unscaled := -1, scale := 0 } 0) =
    (some [{ targetField := { field := whole.id, path := [1] }
             outcome := .accepted { unscaled := -1, scale := 0 } },
           { targetField := { field := whole.id, path := [2] }
             outcome := .accepted { unscaled := -1, scale := 0 } }],
     some [{ targetField := { field := whole.id, path := [1] }
             outcome := .accepted { unscaled := -1, scale := 0 } },
           { targetField := { field := whole.id, path := [2] }
             outcome := .accepted { unscaled := -1, scale := 0 } }],
     some []) := by
  native_decide

/- The declared range refuses per row and keeps the **exact attempted value uncapped** rather than
clamping to the maximum, dropping the write, or refusing once for the whole group. Measured on kernel
30.8.1, where the same shape reports `value='99'` with `errored` set and no clear at each row. The
in-range control on the same target separates the refusal from the carrier itself. -/
example : (outcomes? ["Probe"] bounded.id { unscaled := 99, scale := 0 } 2,
    outcomes? ["Probe"] bounded.id { unscaled := 5, scale := 0 } 1) =
    (some [{ targetField := { field := bounded.id, path := [1] }
             outcome := .rejected { unscaled := 99, scale := 0 } .aboveMaximum },
           { targetField := { field := bounded.id, path := [2] }
             outcome := .rejected { unscaled := 99, scale := 0 } .aboveMaximum }],
     some [{ targetField := { field := bounded.id, path := [1] }
             outcome := .accepted { unscaled := 5, scale := 0 } }]) := by
  native_decide

/- The two refusal grounds are checked at **different times**, and that is the shape of this family.
Excess decimal scale is an authoring gate carrying a Kernel identity, so an over-scale constant has
no rows at all; an out-of-range constant elaborates and fails per row above. The in-scale control
keeps the gate from reading as a blanket refusal of the target. -/
example : (kernelCode? ["Probe"] whole.id { unscaled := 15, scale := 1 },
    (checkRepeatableNumberConstantComputation model ["Probe"] whole.id
      { unscaled := -1, scale := 0 }).toOption.isSome,
    (checkRepeatableNumberConstantComputation model ["Probe"] bounded.id
      { unscaled := 99, scale := 0 }).toOption.isSome) =
    (some "MVK_INVALID_COMPARE_DEC_PLACES", true, true) := by
  native_decide

/- Scale is read **twice, differently**, and the store is the half that normalizes. Both `1.5` and
`1.50` into the same two-digit target store `1.5`, so trailing zeros are stripped rather than
retained; into a target that *requires* two digits, `1.5` becomes `1.50` and `10` becomes `10.00`.
All four are measured on kernel 30.8.1 and agree on both codegen strategies. The pair of targets is
what separates the two directions: a carrier that only retained, or only padded, matches one column
and fails the other. -/
example : (outcomes? ["Probe"] cents.id { unscaled := 15, scale := 1 } 1,
    outcomes? ["Probe"] cents.id { unscaled := 150, scale := 2 } 1,
    outcomes? ["Probe"] padded.id { unscaled := 15, scale := 1 } 1,
    outcomes? ["Probe"] padded.id { unscaled := 10, scale := 0 } 1) =
    (some [{ targetField := { field := cents.id, path := [1] }
             outcome := .accepted { unscaled := 15, scale := 1 } }],
     some [{ targetField := { field := cents.id, path := [1] }
             outcome := .accepted { unscaled := 15, scale := 1 } }],
     some [{ targetField := { field := padded.id, path := [1] }
             outcome := .accepted { unscaled := 150, scale := 2 } }],
     some [{ targetField := { field := padded.id, path := [1] }
             outcome := .accepted { unscaled := 1000, scale := 2 } }]) := by
  native_decide

/- The authoring gate reads the **authored** scale, and stripping never feeds back into it: `1.50`
into a scale-0 target is refused even though its stored form would have been the integer `1`, while
the same literal into the two-digit target above is admitted and then stripped. The kernel's own
refusal text names two fractional digits on the right-hand side, so this is the gate counting the
zero rather than an ordering accident. -/
example : (kernelCode? ["Probe"] whole.id { unscaled := 150, scale := 2 },
    (checkRepeatableNumberConstantComputation model ["Probe"] cents.id
      { unscaled := 150, scale := 2 }).toOption.isSome) =
    (some "MVK_INVALID_COMPARE_DEC_PLACES", true) := by
  native_decide

/- Placement is containment: the target's own group and every ancestor admit it, and only a group the
target does not lie below is refused — with the Kernel identity that refusal actually carries. -/
example : ([["Probe", "Tasks"], ["Probe"]].map fun group =>
      (checkRepeatableNumberConstantComputation model group whole.id
        { unscaled := 1, scale := 0 }).toOption.isSome,
    kernelCode? ["Probe", "Store"] whole.id { unscaled := 1, scale := 0 }) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- A nonrepeatable target belongs to no carrier here and is declined by the shared certificate rather
than by a second local gate, so it claims no Kernel class. -/
example : (match checkRepeatableNumberConstantComputation model ["Probe"] note.id
      { unscaled := 1, scale := 0 } with
    | .error cause => (cause.diagnostic?.isSome, true)
    | .ok _ => (false, false)) = (false, true) := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberConstantComputation
