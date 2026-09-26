import A12Kernel.Elaboration.DateRangeOverlap
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TokenValuesNotUnique

/-! # The entity list's category gate

An entity list whose carrier refuses a category draws `MVK_CATEGORY_NOT_ALLOWED` for an
Enumeration's category, and where the gate stands against the list's repeat depends on the carrier:
the counts ask it ahead of the repeat, the other carriers behind the repeat and the root gate
([inbound](../../docs/SOURCES.md#inbound-2026-09-26b-entity-list-category), `kf482`). Of the 22
operators the peer measures, three Lean carriers spell a category operand: the token
`FieldValuesNotUnique`, the token `NumberOfDifferentValues` and `DateRangesOverlap`. The fixture
mirrors the peer's `/Order`, every rule declared at the root.
-/

namespace A12Kernel.Conformance.EntityListCategoryGate

open A12Kernel

private def tiers : EnumerationDeclaration :=
  { storedTokens := ["GOLD", "SILVER"], categories := [{ name := "Level", tokens := ["HI", "LO"] }] }

private def orderModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order"], name := "Reference", policy := { kind := .string } },
      { id := 2, groupPath := ["Order"], name := "Label", policy := { kind := .string } },
      { id := 3, groupPath := ["Order"], name := "Tier", policy := { kind := .enumeration },
        enumeration := some tiers },
      { id := 4, groupPath := ["Order"], name := "Window", policy := { kind := .dateRange },
        dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } },
      { id := 5, groupPath := ["Order", "Billing"], name := "Net",
        policy := { kind := .number { scale := 0, signed := false } } },
      { id := 6, groupPath := ["Order", "Contact"], name := "Email", policy := { kind := .string } }] }

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def level (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name } (.projected "Level")

private inductive Decision where
  | admitted
  | mapped (diagnostic : KernelStaticDiagnostic)
  | rejectedUnmapped
  deriving Repr, DecidableEq

private def decide (result : Except ε α) (diagnostic? : ε → Option KernelStaticDiagnostic) :
    Decision :=
  match result with
  | .ok _ => .admitted
  | .error error =>
      match diagnostic? error with
      | some diagnostic => .mapped diagnostic
      | none => .rejectedUnmapped

private def notUnique (first : SurfaceFieldEntityOperand) (rest : List SurfaceFieldEntityOperand) :
    Decision :=
  decide (elaborateTokenValuesNotUniqueSource orderModel ["Order"] { first, rest })
    TokenValuesNotUniqueElabError.diagnostic?

private def distinct (first : SurfaceFieldEntityOperand) (rest : List SurfaceFieldEntityOperand) :
    Decision :=
  decide (elaborateTokenDistinctCountSource orderModel ["Order"] { first, rest })
    TokenDistinctCountElabError.diagnostic?

private def overlap (first : SurfaceFieldEntityOperand) (rest : List SurfaceFieldEntityOperand) :
    Decision :=
  decide (elaborateDateRangesOverlapSource orderModel ["Order"] { first, rest })
    DateRangesOverlapElabError.diagnostic?

/- **Each carrier refuses the category, and its place against the repeat is its own.**
   `FieldValuesNotUnique` asks the repeat first, so beside a repeated `Label` the duplicate class
   answers, while `NumberOfDifferentValues` asks the category first and keeps its class there.
   `FieldValuesNotUnique` asks the category ahead of its mixing gate, which would refuse `Tier`'s
   category beside a String too, and `DateRangesOverlap` ahead of its own DateRange kind gate. The
   category-free lists are admitted. -/
example :
    [notUnique (level "Tier") [field "Label"], notUnique (level "Tier") [field "Label", field "Label"],
      notUnique (field "Reference") [field "Label"],
      distinct (level "Tier") [field "Label"], distinct (level "Tier") [field "Label", field "Label"],
      distinct (field "Tier") [field "Label"],
      overlap (field "Window") [level "Tier"]] =
    [.mapped .categoryNotAllowed, .mapped .duplicateParam1, .admitted,
      .mapped .categoryNotAllowed, .mapped .categoryNotAllowed, .admitted,
      .mapped .categoryNotAllowed] := by
  native_decide

/- The category is part of the operand's identity for the repeat, so a category beside its own
   field uncategorized repeats nothing and draws the category class. The peer measures this on
   `AllFieldsFilled`, whose carrier `FieldValuesNotUnique` shares. -/
example : notUnique (level "Tier") [field "Tier"] = .mapped .categoryNotAllowed := by
  native_decide

/- `FirstFilledValue`'s carrier asks no category gate by the peer's source reading, and no row
   measures what it draws, so this route keeps admitting the category: the gate is a carrier's, not
   the shared shape's. -/
example :
    decide (elaborateFirstFilledTokenSource orderModel ["Order"] { first := level "Tier", rest := [field "Label"] })
      (fun error => error.diagnostic?) = .admitted := by
  native_decide

end A12Kernel.Conformance.EntityListCategoryGate
