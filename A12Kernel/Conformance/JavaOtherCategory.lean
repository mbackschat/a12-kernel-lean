import A12Kernel.Elaboration.JavaOtherCategory

/-! # The pinned `\p{C}` table

Locks the generated table against an edit: its range count and code-point total as measured on
OpenJDK 21.0.12.1 on 2026-09-26, its order with a gap between neighbours, the binary search against a
linear scan on both sides of every boundary, and the rows the peer put to the Kernel
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-message-characters)). -/

namespace A12Kernel.Conformance.JavaOtherCategory

open A12Kernel

private def linearMember (point : Nat) : Bool :=
  javaOtherCategoryRanges.any fun (low, high) => low ≤ point && point ≤ high

private def searchedMember (point : Nat) : Bool :=
  javaOtherCategoryRanges.binSearchContains (point, point) (fun left right => left.2 < right.1)

example :
    javaOtherCategoryRanges.size = 712 ∧
    javaOtherCategoryRanges.foldl (fun total (low, high) => total + (high + 1 - low)) 0 = 965096 := by
  native_decide

/- Each range is well formed and ends at least two code points before the next begins, which is what
   a maximal range list is and what the search's order needs. -/
example :
    javaOtherCategoryRanges.all (fun (low, high) => low ≤ high) ∧
    (javaOtherCategoryRanges.toList.zip javaOtherCategoryRanges.toList.tail).all
      (fun ((_, high), (low, _)) => high + 1 < low) := by
  native_decide

example :
    javaOtherCategoryRanges.all fun (low, high) =>
      [low - 1, low, high, high + 1].all fun point => searchedMember point == linearMember point := by
  native_decide

/- The rows measured on the Kernel: the format, private-use and unassigned characters and both
   supplementary ones inside the set, the two Unicode separators, the no-break space and a
   supplementary letter outside it. -/
example :
    [0x85, 0xAD, 0x200B, 0xFEFF, 0x200E, 0xE000, 0x378, 0xF0000, 0xE0001].all
      (fun point => isJavaOtherCategory (Char.ofNat point)) ∧
    [0x2028, 0x2029, 0xA0, 0x1F600, 0x41].all
      (fun point => !isJavaOtherCategory (Char.ofNat point)) := by
  native_decide

end A12Kernel.Conformance.JavaOtherCategory
