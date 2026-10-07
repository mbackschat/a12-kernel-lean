import A12Kernel.Semantics.MessageIndex

namespace A12Kernel.Conformance.MessageIndex

open A12Kernel

private def cache : MessageIndexCache := {
  insertions := [
    { group := 10, parentPath := [1], key := .text "a", row := 3 },
    { group := 11, parentPath := [1], key := .text "b", row := 4 },
    { group := 10, parentPath := [2], key := .text "b", row := 5 },
    { group := 10, parentPath := [1], key := .text "a", row := 2 },
    { group := 10, parentPath := [1], key := .text "A", row := 6 },
    { group := 10, parentPath := [1], key := .text " a", row := 7 },
    { group := 10, parentPath := [1], key := .number (1 / 2), row := 8 }]
}

example : cache.lookup 10 [1] (some (.text "a")) = .concrete 2 := by
  native_decide

example : cache.lookup 11 [1] (some (.text "b")) = .concrete 4 ∧
    cache.lookup 10 [2] (some (.text "b")) = .concrete 5 ∧
    cache.lookup 10 [1] (some (.text "b")) = .unknown := by
  native_decide

example : cache.lookup 10 [1] none = .unknown ∧
    cache.lookup 10 [1] (some (.text "")) = .unknown ∧
    cache.lookup 10 [1] (some (.text "missing")) = .unknown := by
  native_decide

example : cache.lookup 10 [1] (some (.text "A")) = .concrete 6 ∧
    cache.lookup 10 [1] (some (.text " a")) = .concrete 7 ∧
    cache.lookup 10 [1] (some (.text "a ")) = .unknown := by
  native_decide

example : cache.lookup 10 [1] (some (.number (2 / 4))) = .concrete 8 ∧
    cache.lookup 10 [1] (some (.text "0.5")) = .unknown := by
  native_decide

example :
    let extended : MessageIndexCache := {
      insertions := cache.insertions ++ [
        { group := 10, parentPath := [1], key := .text "b", row := 9 },
        { group := 11, parentPath := [1], key := .text "a", row := 10 },
        { group := 10, parentPath := [2], key := .text "a", row := 11 }] }
    extended.lookup 10 [1] (some (.text "a")) = .concrete 2 := by
  native_decide

end A12Kernel.Conformance.MessageIndex
