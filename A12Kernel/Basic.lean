/-! # A12Kernel.Basic — smoke module

A trivial module that proves the toolchain is wired end to end. The real content
lives in `A12Kernel.Core` and the modules the staged build order
(`docs/LEAN-ENCODING-GUIDE.md` §3) adds next. -/

namespace A12Kernel

/-- The kernel version whose *observable behaviour* this specification tracks
    (see `spec/SEMANTICS-MAP.md` §0), kernel 31.3.1 since the owner-decided migration of
    2026-11-07 (`docs/PLAN.md`, kernel 31.3.1 migration). The 31.1.1 and 30.8.1 accounts are the
    tags `kernel-31.1.1-final` and `kernel-30.8.1-final`. -/
def kernelVersion : String := "31.3.1"

/-- The kernel version the frozen retained bundles under `evidence/kernel-30.8.1` were
    captured on. They are replayed against the theory of `kernelVersion` and are never
    restamped on disk (`docs/EVIDENCE.md`, Evolution). -/
def retainedEvidenceKernelVersion : String := "30.8.1"

#eval kernelVersion

end A12Kernel
