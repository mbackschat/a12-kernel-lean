import A12Kernel.Elaboration.IndexParameterResolution

/-! # Locks on the `index(...)` parameter's resolution and repeatability stages

The resolution classes, the not-iterating class, and the non-repeatable branch's whole admitting matrix
are measured; the composed-index and repeatability-mismatch classes are source-derived and honestly
unwitnessed ([resolution](../../docs/sources/message-and-pointer-probes.md#src-index-terminal-refusal-classes),
[non-repeatable gate](../../docs/sources/message-and-pointer-probes.md#src-nonrepeatable-index-field-gate)).

The matrix separates the resolution cascade's internal order, resolution's independence from the
condition, the mismatch class in **both** directions, the two branch-local classes against each other,
the non-repeatable admitting shape conjunct by conjunct, and the scan's first-match-wins order.
-/

namespace A12Kernel.Conformance.IndexParameterResolution

open A12Kernel

private def key? (available : Bool) (path : ErrorPathIndexFields)
    (referenced : List ReferencedIndexField) : Option String :=
  (indexParameterRefusal available path referenced).map KernelStaticDiagnostic.kernelCode

/-- A referenced field that agrees with a repeatable error path and iterates. -/
private def iteratingRow : ReferencedIndexField := {}

/-- The Enumeration shape the non-repeatable branch admits. -/
private def admittingEnum : ReferencedIndexField :=
  { repeatable := false, fieldType := .enumeration 1 true }

/- **The resolution cascade's order, with the condition held empty so only stage one can speak.** An
   unresolvable name outranks a composed index on the very same path, so the two cannot be read as
   independent tests. The empty and several-candidate guards are **disjoint**, so their relative order is
   not observable and no row below attempts to pin it — a mutation swapping those two is equivalent
   rather than uncaught. -/
example :
    key? true { matching := 0 } [] = some "INVALID_INDEX_FIELD" ∧
      key? true { matching := 2 } [] = some "INVALID_INDEX_FIELD_AMBIGUOUS" ∧
      key? true { declaredNamesOnGroup := 2 } [] = some "INVALID_INDEX_FIELD_COMPOSED_INDEX" ∧
      key? true { matching := 0, declaredNamesOnGroup := 2 } [] = some "INVALID_INDEX_FIELD" ∧
      key? true {} [] = none := by
  native_decide

/- **Resolution never consults the condition.** The same unresolvable path reports its class against an
   empty referenced set and against one whose every member would refuse on its own. -/
example :
    key? true { matching := 0 } [] = some "INVALID_INDEX_FIELD" ∧
      key? true { matching := 0 }
        [{ repeatable := false }, { iterating := false }] = some "INVALID_INDEX_FIELD" := by
  native_decide

/- **The mismatch class fires in both directions, and it is symmetric under swapping the two
   repeatability flags.** The two rows differ in which side repeats and report one class; the two
   agreeing rows beneath them are the controls that keep the class on the disagreement. -/
example :
    key? true { groupRepeatable := false } [iteratingRow] =
        some "INVALID_INDEX_FIELD_REP" ∧
      key? true { groupRepeatable := true } [{ repeatable := false }] =
        some "INVALID_INDEX_FIELD_REP" ∧
      key? true { groupRepeatable := true } [iteratingRow] = none ∧
      key? true { groupRepeatable := false } [admittingEnum] = none := by
  native_decide

/- **The two branch-local classes are reachable from opposite branches only.** A non-iterating read and
   a type the non-repeatable gate rejects are carried by one and the same referenced row, so the branch
   is the only thing that moves. -/
example :
    key? true { groupRepeatable := true }
        [{ iterating := false, fieldType := .other }] = some "INVALID_INDEX_FIELD_REP_ITER" ∧
      key? true { groupRepeatable := false }
        [{ repeatable := false, iterating := false, fieldType := .other }] =
        some "INVALID_INDEX_FIELD_NONREP_ENUM" := by
  native_decide

/- **The declared type is read on the non-repeatable branch and nowhere else.** The identical
   non-Enumeration type is admitted under a repeatable error path and refused under a non-repeatable
   one — the control that stops the refusal being attributed to the field's kind, replaying the measured
   repeatable-carrier row. -/
example :
    key? true { groupRepeatable := true } [{ fieldType := .other }] = none ∧
      key? true { groupRepeatable := false }
        [{ repeatable := false, fieldType := .other }] = some "INVALID_INDEX_FIELD_NONREP_ENUM" := by
  native_decide

/- **The measured non-repeatable matrix, conjunct by conjunct.** One value with its s-value set is
   admitted; two values, a missing s-value, and a non-Enumeration each refuse. The last row is
   over-determined by construction and is not evidence for the Enumeration conjunct on its own. -/
example :
    key? true { groupRepeatable := false } [admittingEnum] = none ∧
      key? true { groupRepeatable := false }
        [{ repeatable := false, fieldType := .enumeration 2 true }] =
        some "INVALID_INDEX_FIELD_NONREP_ENUM" ∧
      key? true { groupRepeatable := false }
        [{ repeatable := false, fieldType := .enumeration 1 false }] =
        some "INVALID_INDEX_FIELD_NONREP_ENUM" ∧
      key? true { groupRepeatable := false }
        [{ repeatable := false, fieldType := .other }] =
        some "INVALID_INDEX_FIELD_NONREP_ENUM" := by
  native_decide

/- **A zero-value Enumeration refuses too**, which keeps the count test an equality rather than an upper
   bound — the nearest false generalization to `valueCount ≤ 1`. -/
example :
    key? true { groupRepeatable := false }
      [{ repeatable := false, fieldType := .enumeration 0 true }] =
      some "INVALID_INDEX_FIELD_NONREP_ENUM" := by
  native_decide

/- **An empty referenced set skips the stage**, so a parameter is admitted beside a condition that never
   mentions the index field it names — and the same path with one offending member refuses, which is
   what keeps the empty row from reading as a vacuous pass. -/
example :
    key? true { groupRepeatable := false } [] = none ∧
      key? true { groupRepeatable := false } [iteratingRow] = some "INVALID_INDEX_FIELD_REP" := by
  native_decide

/- **The scan reports its first refusal, not its worst.** One list read under both branches reports the
   class of whichever member comes first, so a consumer cannot infer the set's other defects. -/
example :
    key? true { groupRepeatable := true }
        [{ iterating := false }, { repeatable := false }] =
        some "INVALID_INDEX_FIELD_REP_ITER" ∧
      key? true { groupRepeatable := true }
        [{ repeatable := false }, { iterating := false }] =
        some "INVALID_INDEX_FIELD_REP" := by
  native_decide

/- **The availability gate suppresses every class above**, including one that needs no condition at
   all — so an unparseable condition admits a parameter whose own path is unresolvable. -/
example :
    key? false { matching := 0 } [] = none ∧
      key? false { groupRepeatable := false } [iteratingRow] = none := by
  native_decide

end A12Kernel.Conformance.IndexParameterResolution
