import A12Kernel.Conformance.TokenEntityValueList

/-! # Mixed String entity-list consumer probe

This module keeps the bounded Execute/Transform/Explain projection separate from the
family's behavioral conformance matrix.
-/

namespace A12Kernel.Conformance.TokenEntityValueList

/- Nested and outer String stars preserve independent canonical environments, hierarchical extent, exact stored CRLF spelling, normalized evaluated text, and authored order. -/
example :
    inspectForConsumer storedConsumerQuery =
      .available {
        family := .string
        fields := [
          { field := 6
            projection := none
            topology := some [
              [(10, 1), (20, 1)],
              [(10, 1), (20, 2)],
              [(10, 2), (20, 1)]]
            openTail := true
            addressed := [
              ({ field := 6, path := [1, 1] }, some "N11"),
              ({ field := 6, path := [1, 2] }, some "N12"),
              ({ field := 6, path := [2, 1] }, some "N21")]
            projected := [
              .present "N11", .present "N12", .present "N21"] },
          { field := 4
            projection := none
            topology := some [[(10, 1)], [(10, 2)]]
            openTail := false
            addressed := [
              ({ field := 4, path := [1] }, some "A\r\nB"),
              ({ field := 4, path := [2] }, some "SECOND")]
            projected := [.present "A\nB", .present "SECOND"] }]
        values := [
          { field := 2
            projection := none
            topology := none
            openTail := false
            addressed := [({ field := 2, path := [] }, some "MATCH")]
            projected := [.present "MATCH"] },
          { field := 3
            projection := none
            topology := none
            openTail := false
            addressed := [({ field := 3, path := [] }, some "SPARE")]
            projected := [.present "SPARE"] }]
        verdict := .notFired } := by
  native_decide

end A12Kernel.Conformance.TokenEntityValueList
