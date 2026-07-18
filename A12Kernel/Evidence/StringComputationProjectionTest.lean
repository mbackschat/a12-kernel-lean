import A12Kernel.Evidence.StringComputationProjection

/-! # Compact root-String evidence mutation locks

These focused mutations exercise only distinctions owned by the typed family. Generic JSON, path, digest, and bounded-file behavior remains in `ObservationBundleTest`.
-/

namespace A12Kernel.Evidence.StringComputationProjectionTest

open A12Kernel
open A12Kernel.Evidence.StringComputationProjection

private def coercedEmptySentinel : StoredString := {
  text := " "
  nonempty := by decide }

private def storeCoercedEmpty : StringTerm → StringStore
  | .text "" => .produced coercedEmptySentinel
  | term => term.store

private def acceptProduced (_ : StringTargetLengthPolicy) : StringStore → StringTargetCheckResult
  | .produced value => .supported (.accepted value)
  | .noValue => .supported .noValue
  | .poison cause => .supported (.poison cause)

private def flipTooLong (policy : StringTargetLengthPolicy)
    (store : StringStore) : StringTargetCheckResult :=
  match policy.check store with
  | .supported (.errored attempted .tooLong) =>
      .supported (.errored attempted .tooShort)
  | result => result

private def reportEqual (outcome : StringTargetOutcome)
    (prior : PriorStringTarget) : Option StringDelta :=
  match outcome with
  | .accepted value => some (.value value)
  | _ => outcome.projectDelta prior

private def collapseAbsent (outcome : StringTargetOutcome)
    (prior : StringTargetState) : StringTargetState :=
  match outcome.applyTo prior with
  | .absent => .presentEmpty
  | state => state

private def expectMismatches (label : String) (expected : List String)
    (runner : Runner) (cases : List Case) : IO Unit :=
  match mismatchIds runner cases with
  | .error error => throw (IO.userError s!"{label}: {error}")
  | .ok actual =>
      if actual != expected then
        throw (IO.userError s!"{label}: mismatched {repr actual}, expected {repr expected}")
      else pure ()

def checkIo (root : System.FilePath) : IO Unit := do
  let cases ← loadCases root
  expectMismatches "natural String replay" [] naturalRunner cases
  expectMismatches "validation-style row gate"
    ["suffix-empty-target-absent-empty-row"]
    { naturalRunner with evaluateRow := id } cases
  expectMismatches "final empty coerced to a stored sentinel"
    ["all-empty-target-stale-content", "all-empty-target-absent-content",
      "all-empty-target-absent-empty-row"]
    { naturalRunner with store := storeCoercedEmpty } cases
  expectMismatches "target constraints bypassed"
    ["max3-stale-errored", "max3-absent-errored", "max3-equal-errored",
      "min5-short-errored"]
    { naturalRunner with check := acceptProduced } cases
  expectMismatches "too-long cause changed"
    ["max3-stale-errored", "max3-absent-errored", "max3-equal-errored"]
    { naturalRunner with check := flipTooLong } cases
  expectMismatches "accepted equality reported changed"
    ["direct-filled-target-equal", "max4-equal-unchanged"]
    { naturalRunner with project := reportEqual } cases
  expectMismatches "absent error application collapsed"
    ["max3-absent-errored"]
    { naturalRunner with apply := collapseAbsent } cases

end A12Kernel.Evidence.StringComputationProjectionTest
