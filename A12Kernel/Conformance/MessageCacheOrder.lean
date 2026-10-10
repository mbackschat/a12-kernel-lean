import A12Kernel.Elaboration.CheckedMessageCache

namespace A12Kernel.Conformance.MessageCacheOrder

open A12Kernel

example : messageCacheLoadCapacity 13 = 16 ∧ messageCacheLoadCapacity 14 = 32 ∧
    messageCacheLoadCapacity 25 = 32 ∧ messageCacheLoadCapacity 26 = 64 ∧
    messageCacheLoadCapacity 49 = 64 ∧ messageCacheLoadCapacity 50 = 128 := by
  native_decide

-- Independent weighted-word arithmetic at the [cache-population checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-cache-population-order) separates UTF-16 hashing from code-point hashing.
example : (messageIdentifierHash "Id" [1, 1, 1, 1]).toNat = 917190150 ∧
    (messageIdentifierHash "Id" [1, 1, 2, 1]).toNat = 917219941 ∧
    (messageIdentifierHash "Key_0" [1, 1, 1]).toNat = 2273772656 ∧
    (messageIdentifierHash "Key_0" [1, 2, 1]).toNat = 2273802447 ∧
    (messageIdentifierHash "/Form/Rows" [1, 1]).toNat = 2298849708 ∧
    (messageIdentifierHash "😀" [1, 2, 1]).toNat = 84602876 ∧
    messageNameUnits "😀" = [55357, 56832] := by
  native_decide

example : messageCacheBucket 32 917190150 = 13 ∧
    messageCacheBucket 32 917219941 = 14 ∧
    messageCacheBucket 64 917190150 = 45 ∧
    messageCacheBucket 64 917219941 = 14 ∧
    messageCacheBucket 16 2273772656 = 7 ∧
    messageCacheBucket 16 2273802447 = 8 ∧
    messageCacheBucket 32 2273772656 = 23 ∧
    messageCacheBucket 32 2273802447 = 8 := by
  native_decide

private def association (row : Nat) : MessageIndexInsertion :=
  { group := 10, parentPath := [1], key := .text "same", row }

private def indexed (hash : UInt32) (row : Nat) : MessageCachePopulationEntry :=
  { hash, association := some (association row) }

private def filler (hash : UInt32) : MessageCachePopulationEntry := { hash }

private def lookupResult (population : List MessageCachePopulationEntry)
    (group : RepeatableLevel) (parentPath : List Nat) (key : SemanticIndexKey) :
    Option MessageRepetitionCoordinate := do
  let cache ← (deriveMessageIndexCache population).toOption
  pure (cache.lookup group parentPath (some key))

private def errorResult (population : List MessageCachePopulationEntry)
    (rowOrder : MessageCacheRowOrder := .unknown) :
    Option MessageCacheOrderError :=
  match deriveMessageIndexCache population rowOrder with
  | .ok _ => none
  | .error error => some error

example : (deriveMessageIndexCache []).toOption = some { insertions := [] } := by
  native_decide

private def uniqueSameBucket : List MessageCachePopulationEntry :=
  (List.range 8).map fun index =>
    { hash := 0, association := some {
        group := 10, parentPath := [1], key := .text s!"key{index}", row := index + 1 } }

example : lookupResult uniqueSameBucket 10 [1] (.text "key0") = some (.concrete 1) ∧
    lookupResult uniqueSameBucket.reverse 10 [1] (.text "key0") = some (.concrete 1) ∧
    lookupResult uniqueSameBucket 10 [1] (.text "key7") = some (.concrete 8) ∧
    (deriveMessageIndexCache uniqueSameBucket).toOption.map (·.insertions.length) = some 8 := by
  native_decide

private def distinctBuckets : List MessageCachePopulationEntry :=
  [indexed 3 3, indexed 14 1, indexed 1 2]

example : (deriveMessageIndexCache distinctBuckets).toOption = some { insertions := [association 1] } ∧
    (deriveMessageIndexCache distinctBuckets.reverse).toOption = some { insertions := [association 1] } := by
  native_decide

private def lowerBucketTie : List MessageCachePopulationEntry :=
  [indexed 1 2, indexed 17 3, indexed 14 1]

example : (deriveMessageIndexCache lowerBucketTie).toOption = some { insertions := [association 1] } ∧
    (deriveMessageIndexCache lowerBucketTie.reverse).toOption = some { insertions := [association 1] } := by
  native_decide

example : errorResult [indexed 1 1, indexed 17 2] =
      some (.unresolvedBucket 10 [1] (.text "same")) ∧
    (deriveMessageIndexCache [indexed 1 1, indexed 2 2]).toOption =
      some { insertions := [association 2] } := by
  native_decide

private def listBinTie : List MessageCachePopulationEntry := [indexed 1 1, indexed 17 2]

example : (deriveMessageIndexCache listBinTie .ascendingPhysical).toOption =
      some { insertions := [association 1] } ∧
    (deriveMessageIndexCache listBinTie.reverse .ascendingPhysical).toOption =
      some { insertions := [association 1] } := by
  native_decide

private def highestBucketTie : List MessageCachePopulationEntry :=
  [indexed 1 1, indexed 2 3, indexed 18 2]

example : (deriveMessageIndexCache highestBucketTie .ascendingPhysical).toOption =
      some { insertions := [association 2] } ∧
    (deriveMessageIndexCache highestBucketTie.reverse .ascendingPhysical).toOption =
      some { insertions := [association 2] } := by
  native_decide

private def separateNamespaces : List MessageCachePopulationEntry :=
  [indexed 14 1, indexed 1 2,
    { hash := 0, association := some { group := 11, parentPath := [1], key := .text "same", row := 3 } },
    { hash := 0, association := some { group := 10, parentPath := [2], key := .text "same", row := 4 } },
    { hash := 0, association := some { group := 10, parentPath := [1], key := .text "other", row := 5 } },
    { hash := 0, association := some { group := 10, parentPath := [1], key := .number 1, row := 6 } }]

example : lookupResult separateNamespaces 10 [1] (.text "same") = some (.concrete 1) ∧
    lookupResult separateNamespaces 11 [1] (.text "same") = some (.concrete 3) ∧
    lookupResult separateNamespaces 10 [2] (.text "same") = some (.concrete 4) ∧
    lookupResult separateNamespaces 10 [1] (.text "other") = some (.concrete 5) ∧
    lookupResult separateNamespaces 10 [1] (.number 1) = some (.concrete 6) ∧
    (deriveMessageIndexCache separateNamespaces).toOption.map (·.insertions.length) = some 5 := by
  native_decide

private def capacityPair : List MessageCachePopulationEntry := [indexed 15 1, indexed 16 2]

private def loadFillers : List MessageCachePopulationEntry :=
  (List.range 12).map (filler ∘ UInt32.ofNat)

example : (deriveMessageIndexCache capacityPair).toOption = some { insertions := [association 1] } ∧
    (deriveMessageIndexCache (capacityPair ++ loadFillers)).toOption =
      some { insertions := [association 2] } := by
  native_decide

private def earlyCollision : List MessageCachePopulationEntry :=
  capacityPair ++ List.replicate 7 (filler 0)

private def collisionControl : List MessageCachePopulationEntry :=
  capacityPair ++ List.replicate 6 (filler 0) ++ [filler 2]

example : messageCacheCapacities collisionControl = [16] ∧
    messageCacheCapacities earlyCollision = [32] ∧
    (deriveMessageIndexCache earlyCollision).toOption = some { insertions := [association 2] } ∧
    (deriveMessageIndexCache collisionControl).toOption = some { insertions := [association 1] } := by
  native_decide

private def eightEntryGrowth : List MessageCachePopulationEntry :=
  [indexed 0 1, indexed 16 2] ++ List.replicate 6 (filler 0)

example : messageCacheCapacities eightEntryGrowth = [32] ∧
    (deriveMessageIndexCache eightEntryGrowth).toOption = some { insertions := [association 2] } := by
  native_decide

example : messageCacheCapacities
      (List.replicate 4 (filler 0) ++ List.replicate 4 (filler 16)) = [32] ∧
    messageCacheCapacities (List.replicate 8 (filler 0)) = [32] ∧
    messageCacheCapacities (List.replicate 9 (filler 0)) = [64] ∧
    messageCacheCapacities ([filler 16] ++ List.replicate 8 (filler 0)) = [32, 64] ∧
    messageCacheCapacities (List.replicate 8 (filler 0) ++ [filler 16]) = [32, 64] := by
  native_decide

private def capacityDependentWinner : List MessageCachePopulationEntry :=
  [indexed 31 1, indexed 32 2] ++ List.replicate 7 (filler 0)

private def capacityInvariantWinner : List MessageCachePopulationEntry :=
  [indexed 1 1, indexed 2 2] ++ List.replicate 8 (filler 0) ++ [filler 16]

example : messageCacheCapacities capacityDependentWinner = [32, 64] ∧
    errorResult capacityDependentWinner = some .unresolvedCapacity ∧
    messageCacheCapacities capacityInvariantWinner = [32, 64] ∧
    (deriveMessageIndexCache capacityInvariantWinner).toOption =
      some { insertions := [association 2] } := by
  native_decide

private def settledCapacity : List MessageCachePopulationEntry :=
  earlyCollision ++ (List.range 17).map fun index => filler (UInt32.ofNat (index + 32))

example : messageCacheLoadCapacity settledCapacity.length = 64 ∧
    (deriveMessageIndexCache settledCapacity).toOption = some { insertions := [association 2] } := by
  native_decide

private def splitFillers : List MessageCachePopulationEntry :=
  (List.range 42).map fun index => filler (UInt32.ofNat (index + 2))

private def treeHistory : List MessageCachePopulationEntry :=
  [indexed 1 1, indexed 129 2] ++ List.replicate 6 (filler 65) ++ splitFillers

private def neverTreeControl : List MessageCachePopulationEntry :=
  [indexed 1 1, indexed 129 2] ++ List.replicate 5 (filler 65) ++ [filler 2] ++ splitFillers

example : messageCacheCapacities treeHistory = [128] ∧
    errorResult treeHistory .ascendingPhysical =
      some (.unresolvedBucket 10 [1] (.text "same")) ∧
    messageCacheCapacities neverTreeControl = [128] ∧
    (deriveMessageIndexCache neverTreeControl .ascendingPhysical).toOption =
      some { insertions := [association 1] } := by
  native_decide

private def unrelatedTree : List MessageCachePopulationEntry :=
  [indexed 1 1, indexed 129 2] ++ List.replicate 30 (filler 0)

example : messageCacheCapacities unrelatedTree = [64] ∧
    (deriveMessageIndexCache unrelatedTree .ascendingPhysical).toOption =
      some { insertions := [association 1] } := by
  native_decide

private def queryResult (context : MessageIndexContext) (group : RepeatableLevel)
    (parent : List Nat) (key : Option SemanticIndexKey) :
    MessageCacheOrderError ⊕ MessageRepetitionCoordinate :=
  match context.lookup group parent key with
  | .ok coordinate => .inr coordinate
  | .error error => .inl error

private def isolatedHostPopulation : List MessageCachePopulationEntry := treeHistory ++
  [{ hash := 9, association := some { group := 20, parentPath := [1], key := .text "safe", row := 3 } },
   { hash := 10, association := some { group := 10, parentPath := [2], key := .text "same", row := 4 } },
   { hash := 11, association := some { group := 10, parentPath := [1], key := .text "other", row := 5 } }]

example :
    let context := MessageIndexContext.derived isolatedHostPopulation .ascendingPhysical []
    queryResult context 20 [1] (some (.text "safe")) = .inr (.concrete 3) ∧
    queryResult context 10 [2] (some (.text "same")) = .inr (.concrete 4) ∧
    queryResult context 10 [1] (some (.text "other")) = .inr (.concrete 5) ∧
    queryResult context 10 [1] (some (.text "absent")) = .inr .unknown ∧
    queryResult context 10 [1] none = .inr .unknown ∧
    queryResult context 10 [1] (some (.text "")) = .inr .unknown ∧
    queryResult context 10 [1] (some (.text "same")) =
      .inl (.unresolvedBucket 10 [1] (.text "same")) := by native_decide

example :
    let context := MessageIndexContext.derived capacityDependentWinner .ascendingPhysical []
    queryResult context 10 [1] (some (.text "same")) = .inl .unresolvedCapacity ∧
    queryResult context 20 [1] (some (.text "same")) = .inr .unknown ∧
    queryResult (MessageIndexContext.derived (capacityPair ++ loadFillers) .ascendingPhysical [])
      10 [1] (some (.text "same")) = .inr (.concrete 2) := by native_decide

example :
    queryResult (MessageIndexContext.derived treeHistory .ascendingPhysical [association 7])
      10 [1] (some (.text "same")) = .inr (.concrete 7) ∧
    queryResult (MessageIndexContext.known { insertions := [association 2] })
      10 [1] (some (.text "same")) = .inr (.concrete 2) := by native_decide

private def nameField (id : FieldId) (group : String) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Form", group], name, policy := { kind := .string } }

private def reservedNames : FlatModel :=
  { fields := [nameField 1 "Z" "Key", nameField 4 "C" "Unique",
      nameField 3 "B" "Key_0", nameField 2 "A" "Key"] }

example : reservedNames.messageFieldNames =
      [(2, "Key_1"), (3, "Key_0"), (4, "Unique"), (1, "Key_2")] ∧
    { reservedNames with fields := reservedNames.fields.reverse }.messageFieldNames =
      reservedNames.messageFieldNames := by
  native_decide

private def utf16Names : FlatModel :=
  { fields := [nameField 6 "" "Key", nameField 5 "😀" "Key"] }

example : utf16Names.messageFieldNames = [(5, "Key_0"), (6, "Key_1")] := by
  native_decide

private def defaultModel : FlatModel := {
  fields := [{
    id := 1, groupPath := ["Form", "Rows"], name := "Key", repeatableScope := [10],
    policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["A", "B"], defaultStoredToken := some "B" } },
    { id := 2, groupPath := ["Form", "Rows"], name := "Payload", repeatableScope := [10],
      policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 1 }] }

private def preparedDefault (data : DocumentData) (candidate : FlatModel := defaultModel) :
    Option (CheckedIndexPreliminary candidate) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  checked.applyFullIndexPreliminary.toOption

example : ((preparedDefault {
    instantiatedRows := [{ group := 10, path := [1] }], cells := [] }).bind fun preliminary => do
      let population ← preliminary.base.messageCachePopulation.toOption
      let cache ← preliminary.deriveMessageCache.toOption
      pure (population.length, cache.lookup 10 [] (some (.text "B")),
        preliminary.messageQueryKeyAt? { field := 1, path := [1] })) =
    some (1, .concrete 1, some (.text "B")) := by native_decide

example : ((preparedDefault {
    instantiatedRows := (List.range 3).map fun index => { group := 10, path := [index + 1] }
    cells := [{ address := { field := 1, path := [3] }, stored := "A", raw := .parsed (.enum "A") }] }).bind
    fun preliminary => do
      let population ← preliminary.base.messageCachePopulation.toOption
      let cache ← preliminary.deriveMessageCache.toOption
      pure (population.length, cache.lookup 10 [] (some (.text "A")))) =
    some (2, .unknown) := by native_decide

private def partialDefaultSummary (data : DocumentData) (entities : List RelevantEntityPattern) :
    Option (Nat × Nat × MessageRepetitionCoordinate × Option SemanticIndexKey) := do
  let full ← preparedDefault data
  let view ← (full.base.applyPartialGeneratedPreliminary entities).toOption
  let population ← view.messageCachePopulation.toOption
  let cache ← view.deriveMessageCache.toOption
  pure (population.length, cache.insertions.length, cache.lookup 10 [] (some (.text "B")),
    view.messageQueryKeyAt? { field := 1, path := [1] })

example : partialDefaultSummary {
    instantiatedRows := [{ group := 10, path := [1] }], cells := [] }
    [RelevantEntityPattern.allInstances ["Form"]] =
    some (1, 0, .unknown, none) := by native_decide

private def physicalDefaultB : DocumentData := {
  instantiatedRows := [{ group := 10, path := [1] }]
  cells := [{ address := { field := 1, path := [1] }, stored := "B", raw := .parsed (.enum "B") }] }

example : partialDefaultSummary physicalDefaultB [RelevantEntityPattern.allInstances ["Form"]] =
    some (2, 1, .concrete 1, some (.text "B")) ∧
    partialDefaultSummary physicalDefaultB [] = some (0, 0, .unknown, none) := by native_decide

private def defaultRows (tokens : List (Option String)) : DocumentData := {
  instantiatedRows := tokens.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
  cells := tokens.zipIdx.filterMap fun (token, index) => token.map fun stored => {
    address := { field := 1, path := [index + 1] }, stored
    raw := if stored.isEmpty then .presentEmpty else .parsed (.enum stored) } }

private def defaultCacheTwins (data : DocumentData) (candidate : FlatModel := defaultModel) :
    Option (List (Nat × MessageRepetitionCoordinate × Option SemanticIndexKey)) := do
  let full ← preparedDefault data candidate
  let fullPopulation ← full.base.messageCachePopulation.toOption
  let fullCache ← full.deriveMessageCache.toOption
  let view ← (full.base.applyPartialGeneratedPreliminary [RelevantEntityPattern.allInstances ["Form"]]).toOption
  let partialPopulation ← view.messageCachePopulation.toOption
  let partialCache ← view.deriveMessageCache.toOption
  let address : CellAddr := { field := 1, path := [1] }
  pure [
    (fullPopulation.length, fullCache.lookup 10 [] (some (.text "B")), full.messageQueryKeyAt? address),
    (partialPopulation.length, partialCache.lookup 10 [] (some (.text "B")), view.messageQueryKeyAt? address)]

example : [none, some ""].all (fun token => defaultCacheTwins (defaultRows [token]) ==
    some [(1, .concrete 1, some (.text "B")), (1, .unknown, none)]) = true ∧
    defaultCacheTwins (defaultRows [some "B"]) =
      some [(2, .concrete 1, some (.text "B")), (2, .concrete 1, some (.text "B"))] := by native_decide

example : defaultCacheTwins (defaultRows []) = some [(0, .unknown, none), (0, .unknown, none)] ∧
    defaultCacheTwins (defaultRows [none, none]) = some [(2, .unknown, none), (2, .unknown, none)] := by native_decide

private def mandatoryDefaultModel : FlatModel := {
  defaultModel with fields := defaultModel.fields.map fun field =>
    if field.id == 1 then { field with requiredness := some .absoluteOrNearestRepeatableAncestor } else field }

example : defaultCacheTwins (defaultRows [none]) mandatoryDefaultModel =
    some [(1, .unknown, none), (1, .unknown, none)] := by native_decide

private def invalidDefaultWithPayload : DocumentData := {
  defaultRows [some "Z"] with cells := (defaultRows [some "Z"]).cells ++ [
    { address := { field := 2, path := [1] }, stored := "x", raw := .parsed (.str "x") }] }

example : defaultCacheTwins (defaultRows [some "Z"]) =
    some [(1, .concrete 1, none), (1, .unknown, none)] := by native_decide

example : defaultCacheTwins invalidDefaultWithPayload =
    some [(2, .concrete 1, none), (2, .unknown, none)] := by native_decide

private def parentedDefaultModel : FlatModel := { defaultModel with
  fields := defaultModel.fields.map fun field => { field with repeatableScope := [5, 10] }
  repeatableGroups := { level := 5, path := ["Form"], repeatability := some 2 } ::
    defaultModel.repeatableGroups }

example : ((preparedDefault {
    instantiatedRows := [{ group := 5, path := [1] }, { group := 5, path := [2] },
      { group := 5, path := [3] }, { group := 10, path := [3, 1] }], cells := [] }
      parentedDefaultModel).bind fun preliminary =>
      preliminary.deriveMessageCache.toOption.map (·.lookup 10 [3] (some (.text "B")))) =
    some .unknown := by native_decide

private def multilineModel : FlatModel := {
  defaultModel with fields := [{
    id := 1, groupPath := ["Form", "Rows"], name := "Key", repeatableScope := [10],
    policy := { kind := .string }, stringPolicy := { lineBreaksPermitted := true } }, {
    id := 3, groupPath := ["Form"], name := "Query", policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }] }

private def multilineData (keys : List String) (query : String) : DocumentData := {
  instantiatedRows := keys.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
  cells := keys.zipIdx.map (fun (stored, index) => {
    address := { field := 1, path := [index + 1] }, stored, raw := .parsed (.str stored) }) ++
    [{ address := { field := 3, path := [] }, stored := query, raw := .parsed (.str query) }] }

private def multilineCacheLookup (keys : List String) (query : String) :
    Option (MessageRepetitionCoordinate × MessageRepetitionCoordinate × Option SemanticIndexKey) := do
  let full ← preparedDefault (multilineData keys query) multilineModel
  let fullCache ← full.deriveMessageCache.toOption
  let part ← (full.base.applyPartialGeneratedPreliminary
    [RelevantEntityPattern.allInstances ["Form"]]).toOption
  let partialCache ← part.deriveMessageCache.toOption
  let queryAddress : CellAddr := { field := 3, path := [] }
  pure (fullCache.lookup 10 [] (full.messageQueryKeyAt? queryAddress),
    partialCache.lookup 10 [] (part.messageQueryKeyAt? queryAddress),
    full.messageQueryKeyAt? { field := 1, path := [1] })

example : [
    multilineCacheLookup ["a\r\nb"] "a\nb",
    multilineCacheLookup ["a\nb"] "a\r\nb",
    multilineCacheLookup ["a\r\nb"] "a\r\nb",
    multilineCacheLookup ["a\rb"] "a\nb",
    multilineCacheLookup ["a\r\nb", "a\nb"] "a\r\nb"] = [
      some (.concrete 1, .concrete 1, some (.text "a\nb")),
      some (.concrete 1, .concrete 1, some (.text "a\nb")),
      some (.concrete 1, .concrete 1, some (.text "a\nb")),
      some (.unknown, .unknown, some (.text "a\rb")),
      some (.concrete 2, .concrete 2, none)] := by
  native_decide

private def partialMultilineAlias :
    Option (MessageRepetitionCoordinate × Option SemanticIndexKey × Option SemanticIndexKey × CellObservation) := do
  let full ← preparedDefault (multilineData ["a\r\nb", "a\nb"] "a\r\nb") multilineModel
  let part ← (full.base.applyPartialGeneratedPreliminary [
    RelevantEntityPattern.allInstances ["Form", "Query"], {
      path := ["Form", "Rows", "Key"], indices := [.concrete 1, .concrete 2, .concrete 1] }]).toOption
  let cache ← part.deriveMessageCache.toOption
  let .checked selected ← (part.readAuthoredValidation { field := 1, path := [2] }).toOption
    | none
  pure (cache.lookup 10 [] (part.messageQueryKeyAt? { field := 3, path := [] }),
    part.messageQueryKeyAt? { field := 1, path := [1] },
    part.messageQueryKeyAt? { field := 1, path := [2] }, observeCell .validation selected)

example : partialMultilineAlias =
    some (.concrete 2, none, some (.text "a\nb"), .value (.str "a\nb")) := by
  native_decide

private def customPopulationModel : FlatModel := {
  fields := [
    { id := 1, name := "Custom", groupPath := ["Form"], policy := { kind := .string },
      customType := some { name := "CacheProbe" } },
    { id := 2, name := "Other", groupPath := ["Form"], policy := { kind := .string },
      customType := some { name := "CacheProbe" } }] }

private def customPopulationResult (value : Option String) (field : FieldId := 1)
    (relevant : Bool := true) : Option (CheckedMessageCacheError ⊕ Nat) := do
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == "CacheProbe" then some (fun value _ =>
      if value == "OK" then none else some {
        projectCode := if value == "TEST" then "testIDNummer" else "cacheProbe.reject" }) else none }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler customPopulationModel).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := value.toList.map fun value => {
      address := { field, path := [] }, stored := value,
      raw := if value.isEmpty then .presentEmpty else .parsed (.str value) } }).toOption
  let part ← (checked.applyPartialGeneratedPreliminary []).toOption
  let result := if relevant then checked.messageCachePopulation else part.messageCachePopulation
  pure (match result with | .ok population => .inr population.length | .error error => .inl error)

example : customPopulationResult none = some (.inr 0) ∧
    customPopulationResult (some "") = some (.inr 0) ∧
    customPopulationResult (some "OK") = some (.inr 1) ∧
    customPopulationResult (some "BAD") = some (.inr 0) ∧
    customPopulationResult (some "OK") 2 = some (.inr 1) ∧
    customPopulationResult (some "OK") 2 false = some (.inr 0) ∧
    customPopulationResult (some "TEST") = some (.inl (.customAdmission 1)) ∧
    customPopulationResult (some "TEST") 2 = some (.inl (.customAdmission 2)) ∧
    customPopulationResult (some "TEST") 2 false = some (.inr 0) := by
  native_decide

private def topologyModel : FlatModel := {
  fields := [{
    id := 1, groupPath := ["Form", "Rows", "Items"], name := "N",
    repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }] }

private def topologyData : DocumentData := {
  instantiatedRows := [
    { group := 10, path := [1] }, { group := 20, path := [1, 1] },
    { group := 20, path := [1, 2] }, { group := 20, path := [1, 3] },
    { group := 10, path := [2] }, { group := 20, path := [2, 1] },
    { group := 10, path := [3] }, { group := 20, path := [3, 1] }]
  cells := [[1, 1], [1, 3], [2, 1], [3, 1]].map fun path =>
    { address := { field := 1, path }, stored := "1", raw := .parsed (.num 1) } }

private def topologyPopulationSize (relevant : Option (List RelevantEntityPattern)) :
    Option Nat := do
  let full ← preparedDefault topologyData topologyModel
  let population ← match relevant with
    | none => full.base.messageCachePopulation.toOption
    | some entities => do
        let part ← (full.base.applyPartialGeneratedPreliminary entities).toOption
        part.messageCachePopulation.toOption
  pure population.length

private def relevantTopologyLeaf (parent child : Nat) : List RelevantEntityPattern := [{
  path := ["Form", "Rows", "Items", "N"],
  indices := [.concrete 1, .concrete parent, .concrete child, .concrete 1] }]

-- CheckCommand.checkGroup admits relevant in-capacity physical placeholders even when the selected leaf is absent; over-limit ancestry excludes the entire subtree.
example : [
    topologyPopulationSize none,
    topologyPopulationSize (some [.allInstances ["Form"]]),
    topologyPopulationSize (some []),
    topologyPopulationSize (some (relevantTopologyLeaf 1 1)),
    topologyPopulationSize (some (relevantTopologyLeaf 1 2)),
    topologyPopulationSize (some (relevantTopologyLeaf 2 2)),
    topologyPopulationSize (some (relevantTopologyLeaf 1 3)),
    topologyPopulationSize (some (relevantTopologyLeaf 3 1))] =
      [some 7, some 7, some 0, some 3, some 2, some 1, some 1, some 0] := by
  native_decide

end A12Kernel.Conformance.MessageCacheOrder
