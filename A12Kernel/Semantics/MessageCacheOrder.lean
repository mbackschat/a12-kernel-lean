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

private def sameAssociation (left right : MessageIndexInsertion) : Bool :=
  left.group == right.group && left.parentPath == right.parentPath && left.key == right.key

/-- Retain one association per key where the highest bucket has exactly one candidate. Tree/list ordering in lower buckets is immaterial. Equal highest buckets and possible collision-induced early capacity changes require actual host context; neither is guessed. -/
def deriveMessageIndexCache (population : List MessageCachePopulationEntry) :
    Except MessageCacheOrderError MessageIndexCache := do
  let indexed := population.filterMap fun entry => entry.association.map (entry.hash, ·)
  let unique := indexed.all fun (_, association) =>
    (indexed.filter fun (_, other) => sameAssociation association other).length == 1
  if unique then return { insertions := indexed.map Prod.snd }
  let capacity := messageCacheLoadCapacity population.length
  if capacity < 64 && population.any (fun entry =>
      (population.filter fun other => messageCacheBucket 16 entry.hash ==
        messageCacheBucket 16 other.hash).length ≥ 8) then
    throw .unresolvedCapacity
  let mut chosen : List MessageIndexInsertion := []
  for (_, association) in indexed do
    if chosen.any (sameAssociation association) then continue
    let matching := indexed.filter fun (_, other) => sameAssociation association other
    let highest := matching.foldl (fun bucket candidate =>
      max bucket (messageCacheBucket capacity candidate.1)) 0
    match matching.filter (fun candidate => messageCacheBucket capacity candidate.1 == highest) with
    | [(_, winner)] => chosen := chosen ++ [winner]
    | _ => throw (.unresolvedBucket association.group association.parentPath association.key)
  return { insertions := chosen }

end A12Kernel
