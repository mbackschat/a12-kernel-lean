/-! # The iteration order of a Java `HashMap` filled through `computeIfAbsent`

Two kernel 31.1.1 model checks state their findings in the iteration order of a `HashMap` they fill with
`computeIfAbsent`: the uniqueness criteria's shared names, grouped once per criterion, and an Enumeration's
repeated values, collected once per occurrence after the first. That order is the JDK's, not the model's, so
this module re-states the JDK's documented table behaviour once for both consumers: `String.hashCode` over
UTF-16 code units, the spread `h ^ (h >>> 16)`, a power-of-two table created at 16 buckets with a threshold of
three quarters, a new key placed at the head of its bucket, and a resize asked at the start of every call
while the size exceeds the threshold, which splits each bucket into its low and high halves in order. A bucket
reaching eight keys resizes a table below 64 buckets; a tree bucket, which a larger table would form, is not
modelled and keeps the list order, a case no measured row reaches. A `none` key is Java's `null`, hashing to 0.

The values are locked against the peer's measured rows in the two consumers' lock modules.
-/

namespace A12Kernel.JavaHashMap

/-- A string's UTF-16 code units. -/
private def utf16Units (text : String) : List UInt32 :=
  text.toList.flatMap fun character =>
    let scalar : UInt32 := character.val
    if scalar < 0x10000 then [scalar]
    else
      let offset := scalar - 0x10000
      [(0xD800 : UInt32) + (offset >>> 10), (0xDC00 : UInt32) + (offset &&& 0x3FF)]

/-- Java's `String.hashCode`, wrapping at 32 bits, and `null`'s 0. -/
def keyHash : Option String → UInt32
  | none => 0
  | some text => (utf16Units text).foldl (fun hash unit => hash * 31 + unit) 0

/-- The table's hash of a key: the key's hash with its high half folded into the low. -/
def spread (key : Option String) : UInt32 :=
  let hash := keyHash key
  hash ^^^ (hash >>> 16)

private structure Table where
  buckets : Array (List (Option String × UInt32)) := #[]
  size : Nat := 0
  threshold : Nat := 0

/-- Create the 16-bucket table, or double it, each bucket's keys split by the new bit in their order. -/
private def Table.resize (table : Table) : Table :=
  if table.buckets.isEmpty then { table with buckets := Array.replicate 16 [], threshold := 12 }
  else
    let old := table.buckets.size
    let buckets := (List.range old).foldl (init := Array.replicate (2 * old) []) fun buckets index =>
      let (low, high) := (table.buckets[index]!).partition fun (_, hash) => hash.toNat &&& old == 0
      (buckets.set! index low).set! (index + old) high
    { table with buckets, threshold := 2 * table.threshold }

/-- One `computeIfAbsent` call for `key`. -/
private def Table.computeIfAbsent (table : Table) (key : Option String) : Table :=
  let table := if table.buckets.isEmpty || table.threshold < table.size then table.resize else table
  let hash := spread key
  let index := hash.toNat % table.buckets.size
  let bucket := table.buckets[index]!
  if bucket.any (·.1 == key) then table
  else
    let table := { table with buckets := table.buckets.set! index ((key, hash) :: bucket) }
    let table := if 7 ≤ bucket.length && table.buckets.size < 64 then table.resize else table
    { table with size := table.size + 1 }

/-- The keys of a map filled by one `computeIfAbsent` call per element of `calls`, in iteration order. -/
def iterationOrder (calls : List (Option String)) : List (Option String) :=
  ((calls.foldl Table.computeIfAbsent {}).buckets.toList.flatMap (·.map (·.1)))

end A12Kernel.JavaHashMap
