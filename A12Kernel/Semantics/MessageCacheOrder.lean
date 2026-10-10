import A12Kernel.Semantics.MessageIndex

namespace A12Kernel

/-- JVM names are compared and hashed as UTF-16 units, including surrogate pairs. -/
def messageNameUnits (name : String) : List Nat :=
  name.toList.flatMap fun character =>
    let code := character.toNat
    if code < 65536 then [code]
    else [55296 + (code - 65536) / 1024, 56320 + (code - 65536) % 1024]

private def polynomial31 (words : List UInt32) : UInt32 :=
  words.foldl (fun total word => total * 31 + word) 0

/-- Hash the ordinary non-USB identifier profile. Coordinates include fixed groups and the field's own unit coordinate. The weighted-word encoding is independently derived from the identifier contract at the [whole-cache checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-cache-population-order). -/
def messageIdentifierHash (name : String) (coordinates : List Nat) : UInt32 :=
  let coordinateWords := coordinates.map fun coordinate =>
    let word := UInt64.ofNat coordinate
    (word ^^^ (word >>> 32)).toUInt32
  polynomial31 [1, polynomial31 (1 :: coordinateWords),
    polynomial31 ((messageNameUnits name).map UInt32.ofNat), 1]

/-- Bucket coordinate for the observed Java 21 profile; this is not a portable Map-interface guarantee. -/
def messageCacheBucket (capacity : Nat) (hash : UInt32) : Nat :=
  (hash ^^^ (hash >>> 16)).toNat % capacity

/-- Load-only capacity after distinct insertions. The pre-insertion threshold check admits one entry beyond three quarters before the next insertion grows the table. -/
def messageCacheLoadCapacity (population : Nat) : Nat :=
  let rec grow : Nat → Nat → Nat
    | 0, capacity => capacity
    | fuel + 1, capacity =>
        if population ≤ capacity * 3 / 4 + 1 || capacity ≥ 1073741824 then capacity
        else grow fuel (capacity * 2)
  grow population 16

/-- Every admitted field or group contributes a hash; only index fields contribute an association. The producer must supply distinct identifiers from one full-validation population. -/
structure MessageCachePopulationEntry where
  hash : UInt32
  association : Option MessageIndexInsertion := none
  deriving Repr, DecidableEq

inductive MessageCacheOrderError where
  | unresolvedCapacity
  | unresolvedBucket (group : RepeatableLevel) (parentPath : List Nat) (key : SemanticIndexKey)
  deriving Repr, DecidableEq

/-- The caller's established relative insertion order within one indexed group and parent. -/
inductive MessageCacheRowOrder where
  | unknown
  | ascendingPhysical
  deriving Repr, DecidableEq

private def bucketOccupancy (population : List MessageCachePopulationEntry)
    (capacity : Nat) (hash : UInt32) : Nat :=
  (population.filter fun entry =>
    messageCacheBucket capacity entry.hash == messageCacheBucket capacity hash).length

private def peakOccupancy (population : List MessageCachePopulationEntry) (capacity : Nat) : Nat :=
  population.foldl (fun peak entry => max peak (bucketOccupancy population capacity entry.hash)) 0

/-- Capacity possibilities for the observed compute-if-absent profile. Eight colliding insertions force the first growth; nine in one 32-bucket bin force the second. With exactly eight in that bin, insertion timing may distinguish 32 from 64. This envelope never assumes an order among unrelated fields. -/
def messageCacheCapacities (population : List MessageCachePopulationEntry) : List Nat :=
  let load := messageCacheLoadCapacity population.length
  if load ≥ 64 || peakOccupancy population 16 < 8 then [load]
  else
    let peak32 := peakOccupancy population 32
    if population.length ≤ 8 || peak32 < 8 then [32]
    else if peak32 ≥ 9 then [64]
    else [32, 64]

private def sameAssociation (left right : MessageIndexInsertion) : Bool :=
  left.group == right.group && left.parentPath == right.parentPath && left.key == right.key

private def cacheAtCapacity (population : List MessageCachePopulationEntry)
    (capacity : Nat) (rowOrder : MessageCacheRowOrder) :
    Except MessageCacheOrderError MessageIndexCache := do
  let indexed := population.filterMap fun entry => entry.association.map (entry.hash, ·)
  let mut chosen : List MessageIndexInsertion := []
  for (_, association) in indexed do
    if chosen.any (sameAssociation association) then continue
    let matching := indexed.filter fun (_, other) => sameAssociation association other
    let highest := matching.foldl (fun bucket candidate =>
      max bucket (messageCacheBucket capacity candidate.1)) 0
    match matching.filter (fun candidate => messageCacheBucket capacity candidate.1 == highest) with
    | [] => throw (.unresolvedBucket association.group association.parentPath association.key)
    | (hash, first) :: rest =>
        let neverTree := capacity < 64 || bucketOccupancy population 64 hash < 8
        if !rest.isEmpty && !(rowOrder == .ascendingPhysical && neverTree) then
          throw (.unresolvedBucket association.group association.parentPath association.key)
        -- The host prepends list entries and preserves their relative order through resize; ascending physical insertion therefore leaves the earliest row last ([whole-cache checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-cache-population-order)).
        let winner := rest.foldl (fun selected candidate =>
          if candidate.2.row < selected.row then candidate.2 else selected) first
        chosen := chosen ++ [winner]
  return { insertions := chosen }

/-- Derive only associations that agree across the capacity envelope. A unique highest-bucket candidate needs no row-order premise. A tied list bin can use established physical insertion order only when its entire history excludes treeification; other ties require host context. -/
def deriveMessageIndexCache (population : List MessageCachePopulationEntry)
    (rowOrder : MessageCacheRowOrder := .unknown) :
    Except MessageCacheOrderError MessageIndexCache := do
  let indexed := population.filterMap fun entry => entry.association.map (entry.hash, ·)
  let unique := indexed.all fun (_, association) =>
    (indexed.filter fun (_, other) => sameAssociation association other).length == 1
  if unique then return { insertions := indexed.map Prod.snd }
  match messageCacheCapacities population with
  | [] => throw .unresolvedCapacity
  | [capacity] => cacheAtCapacity population capacity rowOrder
  | capacity :: rest =>
      match cacheAtCapacity population capacity rowOrder with
      | .error _ => throw .unresolvedCapacity
      | .ok candidate =>
          if rest.all (fun other => decide ((cacheAtCapacity population other rowOrder).toOption = some candidate)) then
            pure candidate
          else throw .unresolvedCapacity

end A12Kernel
