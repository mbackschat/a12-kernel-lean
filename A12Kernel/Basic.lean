/-! # A12Kernel.Basic — smoke module

A trivial module that proves the toolchain is wired end to end. The real content
lives in `A12Kernel.Core` and the modules the staged build order
(`spec/13-lean-encoding-guide.md` §3) adds next. -/

namespace A12Kernel

/-- The kernel version whose *observable behaviour* this specification tracks
    (see `spec/SEMANTICS-MAP.md` §0). Bump only alongside a deliberate re-pin
    against a newer `../a12-kernel`. -/
def kernelVersion : String := "30.8.1"

#eval kernelVersion

end A12Kernel
