import A12Kernel.Elaboration.StaticDiagnostic

/-! # Kernel static-diagnostic vocabulary laws

These guard the vocabulary itself rather than any operator's use of it. They matter because the vocabulary grows one family at a time: an addition that collided with an existing `MVK_` identifier, or that left the enumeration incomplete, would merge or hide an observable outcome without failing any operator's own cases.
-/

namespace A12Kernel

/-- Distinct classes carry distinct Kernel identifiers. Two constructors sharing one `MVK_` string would silently merge two observable outcomes, so this is checked rather than assumed as the list grows. -/
theorem kernelStaticDiagnostic_kernelCode_nodup :
    (KernelStaticDiagnostic.all.map KernelStaticDiagnostic.kernelCode).Nodup := by
  simp [KernelStaticDiagnostic.all, KernelStaticDiagnostic.kernelCode]

/-- The enumeration is complete, so a consumer may treat `all` as the exact covered surface rather than a curated subset. -/
theorem kernelStaticDiagnostic_mem_all (code : KernelStaticDiagnostic) :
    code ∈ KernelStaticDiagnostic.all := by
  cases code <;> simp [KernelStaticDiagnostic.all]

end A12Kernel
