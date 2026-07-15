/-! # A12Kernel.Semantics.String — shared String primitives -/

namespace A12Kernel

/-- Count UTF-16 code units, matching the JVM/JavaScript kernel boundary rather than Unicode scalar values or grapheme clusters. -/
def utf16CodeUnitLength (value : String) : Nat :=
  value.foldl (fun units character =>
    units + if character.toNat < 0x10000 then 1 else 2) 0

/-- Whether a String contains a CR or LF code point. The reduced target checker handles this earlier than length, so the length-only capsule must fail closed on either form. -/
def containsLineBreak (value : String) : Bool :=
  value.any fun character => character == '\r' || character == '\n'

end A12Kernel
