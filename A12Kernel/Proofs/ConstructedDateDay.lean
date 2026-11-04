import A12Kernel.Semantics.ConstructedDateDay

/-! # Hybrid-calendar day coordinate laws -/

namespace A12Kernel

/-- Exact UTC midnight follows the one-day cutover adjacency of the hybrid label coordinate. -/
theorem constructedDateDay_legacyCutover_instant :
    DateParts.LegacyHybrid.midnightInstant?
        { year := 1582, month := 10, day := 4 } =
      some { epochMillis := -12219379200000 } ∧
    DateParts.LegacyHybrid.midnightInstant?
        { year := 1582, month := 10, day := 15 } =
      some { epochMillis := -12219292800000 } := by
  set_option maxRecDepth 2000 in
    decide

end A12Kernel
