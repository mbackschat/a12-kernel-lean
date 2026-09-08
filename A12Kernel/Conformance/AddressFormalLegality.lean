import A12Kernel.Elaboration.AddressFormalLegality

/-! # Locks on the address gate's positional class rule

The measured rows are the three over-maximum classes on one model, where the same violated level
reports under two different codes depending on which address reports it, and a repeatable root group
reports the serial class everywhere ([checkpoint](../../docs/SOURCES.md#src-address-index-position-classes)).
The under-minimum and index-count rows are the total function this project states rather than measured
behaviour; the module documentation says which is which.
-/

namespace A12Kernel.Conformance.AddressFormalLegality

open A12Kernel

/- **The measured discriminator.** A repeatable root group over its cap reports the serial class on
   its own address, whose vector has length one — so position 0 is also the last position and the row
   class does *not* fire. This is the row that separates the positional rule from "the last index is
   the row", and it is what the Kernel answered on both codegen strategies. -/
example : indexRefusal [3] [2] = some .serialTooLarge := by native_decide

/- Every node beneath that root row reports the serial class too, because the violated level stays at
   position 0 however long the reporting address's vector is. Three vector lengths, one class. -/
example :
    indexRefusal [3, 1] [2, 5] = some .serialTooLarge ∧
      indexRefusal [3, 1, 1] [2, 5, 1] = some .serialTooLarge ∧
      indexRefusal [3, 1, 1, 1] [2, 5, 1, 1] = some .serialTooLarge := by
  native_decide

/- **The same violated level, two codes.** A deeper group over its cap is the last position of its own
   address and an interior position of any descendant's, so one document draws the row class on the
   group and the context class on its field. Both measured on the same probe row. -/
example :
    indexRefusal [1, 3] [2, 2] = some .rowTooLarge ∧
      indexRefusal [1, 3, 1] [2, 2, 1] = some .contextTooLarge := by
  native_decide

/- **First-match-wins over positions is the absorption rule.** With the root and an inner level both
   over their caps, every address reports the outermost violation — so the inner one draws no class of
   its own. Measured on a document where both overflow at once. -/
example : indexRefusal [3, 3] [2, 2] = some .serialTooLarge := by native_decide

/- The accepted control: an in-capacity address at each of those shapes draws nothing. Without it the
   rows above would be consistent with a gate that refuses every address. -/
example :
    indexRefusal [2] [2] = none ∧ indexRefusal [1, 2] [2, 2] = none ∧
      indexRefusal [2, 2, 1] [2, 2, 1] = none := by
  native_decide

/- **Both minimum passes precede every maximum test.** This address is over its cap at position 0 and
   below the minimum at position 1; the minimum class of the *later* position wins. A consumer testing
   both bounds at each position in one walk reports `serialTooLarge` here instead. -/
example : indexRefusal [5, 0] [3, 9] = some .rowTooSmall := by native_decide

/- The same corner on the minimum side: a length-one vector below the minimum is the serial class,
   never the row class. -/
example : indexRefusal [0] [2] = some .serialTooSmall ∧ indexRefusal [1, 0, 1] [2, 2, 1] =
    some .contextTooSmall := by
  native_decide

/- The length gate precedes both bound passes, so a vector that is both miscounted and out of range
   reports the count. Negative coordinates are expressible and are ordinary under-minimum values. -/
example :
    indexRefusal [9, 9] [1] = some .indexCountWrong ∧
      indexRefusal [] [] = none ∧
      indexRefusal [-4] [2] = some .serialTooSmall := by
  native_decide

/- The sub-scope gate's four cells: a declared cap demands a value in range, and no declared cap
   demands no value. The two mismatch directions are different classes. -/
example :
    usbRefusal (some 3) .absent = some .usbMissing ∧
      usbRefusal (some 3) (.supplied 0) = some .usbTooSmall ∧
      usbRefusal (some 3) (.supplied 4) = some .usbTooLarge ∧
      usbRefusal (some 3) (.supplied 3) = none ∧
      usbRefusal none .absent = none ∧
      usbRefusal none (.supplied 1) = some .usbUnexpected := by
  native_decide

/- In an A12 document model no entity declares a sub-scope cap, so only the unexpected-value class
   stays live and a supplied discriminator is refused whatever its magnitude. -/
example :
    usbRefusal a12DeclaredUsbCap .absent = none ∧
      usbRefusal a12DeclaredUsbCap (.supplied 1) = some .usbUnexpected ∧
      usbRefusal a12DeclaredUsbCap (.supplied 99) = some .usbUnexpected := by
  native_decide

/- A failing coordinate vector suppresses the sub-scope gate, and a group entry skips it outright —
   so the identical inputs that refuse a field admit a group. -/
example :
    addressRefusal .field [3] [2] (some 1) (.supplied 9) = some .serialTooLarge ∧
      addressRefusal .field [1] [2] (some 1) (.supplied 9) = some .usbTooLarge ∧
      addressRefusal .group [1] [2] (some 1) (.supplied 9) = none := by
  native_decide

/- Name resolution: a group-only name is a group entry in an ordinary model and an unknown field in a
   unique-entities one. The flag is the whole difference, so a consumer ignoring it reports a class
   the Kernel does not. -/
example :
    resolveEntry .group false = .group ∧ resolveEntry .group true = .unknown ∧
      resolveEntry .field true = .field ∧ resolveEntry .neither false = .unknown := by
  native_decide

/- The unknown-name finding is reported at a **zeroed** address, not the one the document supplied,
   while a supplied-versus-absent discriminator stays distinguishable. Correlating findings to input
   cells by address therefore fails on exactly this class. -/
example :
    unknownFieldReportedAddress [7, 2] (.supplied 5) = ([0, 0], .supplied 0) ∧
      unknownFieldReportedAddress [7, 2] .absent = ([0, 0], .absent) := by
  native_decide

/- Twelve distinct codes, none of them a message-bundle key. The four sub-scope codes are the ones a
   consumer assembling a key by concatenation gets wrong, since three spell the quantity in German and
   one does not. -/
example :
    (AddressRefusal.all.map (·.code)).eraseDups.length = 12 ∧
      AddressRefusal.rowTooLarge.code = "zuGrosseZeile" ∧
      AddressRefusal.usbUnexpected.code = "usbAngegebenBeiMaxUsbNull" := by
  native_decide

end A12Kernel.Conformance.AddressFormalLegality
