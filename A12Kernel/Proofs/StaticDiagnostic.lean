import A12Kernel.Elaboration.StaticDiagnostic

/-! # Kernel static-diagnostic vocabulary laws

These guard the vocabulary itself rather than any operator's use of it. They matter because the vocabulary grows one family at a time: an addition that collided with an existing `MVK_` identifier, or that left the enumeration incomplete, would merge or hide an observable outcome without failing any operator's own cases.
-/

namespace A12Kernel

-- Both checks scan the whole enumeration per class, so their cost grows quadratically with it.
-- Distinctness stays on `simp` because every kernel-checked alternative measured on 2026-10-22
-- at 220 classes was slower: kernel `String` comparison made `decide +kernel` exceed 300 s, and
-- an adjacent-order check cost 74 s. Compiled evaluation would be fast but is excluded from this zone.
set_option maxHeartbeats 400000 in
/-- Distinct classes carry distinct Kernel identifiers. Two constructors sharing one `MVK_` string would silently merge two observable outcomes, so this is checked rather than assumed as the list grows. -/
theorem kernelStaticDiagnostic_kernelCode_nodup :
    (KernelStaticDiagnostic.all.map KernelStaticDiagnostic.kernelCode).Nodup := by
  set_option maxRecDepth 2048 in
    simp [KernelStaticDiagnostic.all, KernelStaticDiagnostic.kernelCode]

/-- The enumeration is complete, so a consumer may treat `all` as the exact covered surface rather than a curated subset. -/
theorem kernelStaticDiagnostic_mem_all (code : KernelStaticDiagnostic) :
    code ∈ KernelStaticDiagnostic.all := by
  -- `decide` compares constructors directly; per-case `simp` cost 22 s here on 2026-10-22, this 2.7 s.
  cases code <;> decide

end A12Kernel
