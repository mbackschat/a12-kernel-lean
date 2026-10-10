import A12Kernel.Semantics.MessageCacheOrder

namespace A12Kernel

@[simp] theorem messageIndex_missingKey
    (cache : MessageIndexCache) (group : RepeatableLevel) (parentPath : List Nat) :
    cache.lookup group parentPath none = .unknown := by
  rfl

@[simp] theorem messageIndex_emptyCache
    (group : RepeatableLevel) (parentPath : List Nat) (key : Option SemanticIndexKey) :
    ({ insertions := [] } : MessageIndexCache).lookup group parentPath key =
      .unknown := by
  cases key with
  | none => rfl
  | some key => simp [MessageIndexCache.lookup]

/-- A matching admitted insertion replaces any earlier association, including a duplicate. -/
theorem messageIndex_append_matching
    (cache : MessageIndexCache) (insertion : MessageIndexInsertion)
    (nonempty : insertion.key ≠ .text "") :
    ({ insertions := cache.insertions ++ [insertion] } : MessageIndexCache).lookup
      insertion.group insertion.parentPath (some insertion.key) =
      .concrete insertion.row := by
  simp [MessageIndexCache.lookup, nonempty, List.foldl_append]

/-- An insertion outside the queried group, parent, or key preserves the association. -/
theorem messageIndex_append_unrelated
    (cache : MessageIndexCache) (insertion : MessageIndexInsertion)
    (group : RepeatableLevel) (parentPath : List Nat) (key : SemanticIndexKey)
    (unrelated : ¬(insertion.group = group ∧ insertion.parentPath = parentPath ∧
      insertion.key = key)) :
    ({ insertions := cache.insertions ++ [insertion] } : MessageIndexCache).lookup
      group parentPath (some key) = cache.lookup group parentPath (some key) := by
  simp [MessageIndexCache.lookup, List.foldl_append, unrelated]

/-- Query isolation keeps all host capacity and collision inputs, including unrelated entries. -/
theorem messageCacheQueryPopulation_hashes (population : List MessageCachePopulationEntry)
    (group : RepeatableLevel) (parent : List Nat) (key : SemanticIndexKey) :
    (messageCacheQueryPopulation population group parent key).map (·.hash) = population.map (·.hash) := by
  simp [messageCacheQueryPopulation, List.map_map]

theorem messageCacheContext_known (cache : MessageIndexCache) (group : RepeatableLevel)
    (parent : List Nat) (key : Option SemanticIndexKey) :
    (MessageIndexContext.known cache).lookup group parent key = .ok (cache.lookup group parent key) := by
  rfl

theorem messageCacheContext_missingKey (context : MessageIndexContext) (group : RepeatableLevel)
    (parent : List Nat) : context.lookup group parent none = .ok .unknown := by
  cases context <;> rfl

end A12Kernel
