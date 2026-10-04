import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.DateRangeOverlap
import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TemporalValuesNotUnique
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.YearlessDateRangeOverlap

/-! # The entity list's category gate

An entity list whose carrier refuses a category draws `MVK_CATEGORY_NOT_ALLOWED` for an
Enumeration's declared category, and where the gate stands against the list's repeat depends on the
carrier: the counts ask it ahead of the repeat and the other carriers behind it, both measured, and
behind the root gate too by the peer's source reading
([inbound](../../docs/SOURCES.md#inbound-2026-09-26b-entity-list-category), `kf482`). Of the 22
operators the peer measures, the Lean carriers that ask it are the three routes of
`FieldValuesNotUnique`, the token `NumberOfDifferentValues`, both `DateRangesOverlap` routes, and
the shared field-fill list on validation and computation. The
fixture is the peer's `/Order` plus a yearless `Season`, a Date `Shipped` and a second root
`Archive`, every rule declared at the root.
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
      { id := 6, groupPath := ["Order", "Contact"], name := "Email", policy := { kind := .string } },
      { id := 7, groupPath := ["Order"], name := "Season", policy := { kind := .dateRange },
        dateRangePolicy := some { format := "MM", separator := "/" } },
      { id := 8, groupPath := ["Order"], name := "Shipped",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 9, groupPath := ["Archive"], name := "Memo", policy := { kind := .string } }] }

private def field (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def category (name category : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name } (.projected category)

private def level (name : String) : SurfaceFieldEntityOperand := category name "Level"

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
   Both rows would otherwise meet a Lean gate that speaks first: `FieldValuesNotUnique`'s mixing
   gate refuses an Enumeration beside a String, and `DateRangesOverlap`'s kind gate a non-DateRange,
   so the category gate stands ahead of each. The category-free lists are admitted. -/
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

private def yearlessOverlap (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) : Decision :=
  decide (elaborateYearlessDateRangesOverlapSource orderModel ["Order"] { first, rest })
    YearlessDateRangesOverlapElabError.diagnostic?

/- The yearless route is the same operator on a yearless range, so it asks the gate where the
   year-bearing route does; no row reads a yearless range, so this lock states that assumption. The
   uncategorized field meets the route's own kind refusal instead, so the category row's class is
   the gate's. -/
example :
    yearlessOverlap (field "Season") [level "Tier"] = .mapped .categoryNotAllowed ∧
      yearlessOverlap (field "Season") [field "Tier"] ≠ .mapped .categoryNotAllowed := by
  native_decide

/- The category is part of the operand's identity for the repeat, so a category beside its own
   field uncategorized repeats nothing and draws the category class. The peer measures this on
   `AllFieldsFilled`; that `FieldValuesNotUnique` answers alike is an assumption resting on the
   peer's source reading that the two share a carrier. -/
example : notUnique (level "Tier") [field "Tier"] = .mapped .categoryNotAllowed := by
  native_decide

/- `FirstFilledValue`'s carrier asks no category gate by the peer's source reading, and no row
   measures what it draws, so this route keeps admitting the category: the gate is a carrier's, not
   the shared shape's. -/
example :
    decide (elaborateFirstFilledTokenSource orderModel ["Order"] { first := level "Tier", rest := [field "Label"] })
      (fun error => error.diagnostic?) = .admitted := by
  native_decide

private def net : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := ["Billing"], field := "Net" }

/- `FieldValuesNotUnique` is one operator whose Number and temporal operands Lean certifies on routes
   of their own, and its measured row places the gate ahead of the mixing gate those routes answer
   for a category beside a Number or a Date. The category-free lists stay admitted. -/
example :
    [decide (elaborateNumberValuesNotUniqueSource orderModel ["Order"]
        { first := net, rest := [level "Tier"] }) NumberValuesNotUniqueElabError.diagnostic?,
      decide (elaborateTemporalValuesNotUniqueSource orderModel ["Order"]
        { first := field "Shipped", rest := [level "Tier"] })
        TemporalValuesNotUniqueElabError.diagnostic?] =
    [.mapped .categoryNotAllowed, .mapped .categoryNotAllowed] := by
  native_decide

private def archiveRoot : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups := ["Archive"] })

/- Two positions no row measures, taken from the peer's source reading of which carriers ask the
   gate behind the repeat and the root gate
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26b-entity-list-category)): `DateRangesOverlap`
   answers a repeated category with the duplicate class, and beside a second model root the root
   gate answers ahead of the category. These locks hold that reading, not a measurement. -/
example :
    [overlap (level "Tier") [level "Tier"], notUnique (level "Tier") [archiveRoot]] =
      [.mapped .duplicateParam1, .mapped .rootGroupReferenced] := by
  native_decide

/- The Number, temporal and yearless routes ask the gate behind the repeat, where the token
   `FieldValuesNotUnique` row measures it: a repeated field ahead of a category draws the duplicate
   class. That these routes share the token row's position rests on the peer's source reading that
   the gate belongs to the operator's carrier, whatever its operands' kind
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26b-entity-list-category)); the yearless route
   rests on the same reading for `DateRangesOverlap`. -/
example :
    [decide (elaborateNumberValuesNotUniqueSource orderModel ["Order"]
        { first := net, rest := [net, level "Tier"] }) NumberValuesNotUniqueElabError.diagnostic?,
      decide (elaborateTemporalValuesNotUniqueSource orderModel ["Order"]
        { first := field "Shipped", rest := [field "Shipped", level "Tier"] })
        TemporalValuesNotUniqueElabError.diagnostic?,
      yearlessOverlap (field "Season") [field "Season", level "Tier"]] =
    [.mapped .duplicateParam1, .mapped .duplicateParam1, .mapped .duplicateParam1] := by
  native_decide

/- A category the Enumeration does not declare is refused as the slot is read, ahead of every list
   gate: beside a String, a Number, a Date or a DateRange, repeated, and on the count carrier that
   asks the category gate first. On an entity list the class is measured on the value-list
   quantifier's field list alone, so its position on these carriers rests on the peer's source
   reading that the category check answers wherever the operand's spec stands. -/
example :
    [notUnique (category "Tier" "Nope") [field "Label"],
      distinct (category "Tier" "Nope") [field "Label"],
      overlap (field "Window") [category "Tier" "Nope"],
      notUnique (category "Tier" "Nope") [category "Tier" "Nope"],
      distinct (category "Tier" "Nope") [category "Tier" "Nope"],
      decide (elaborateNumberValuesNotUniqueSource orderModel ["Order"]
        { first := net, rest := [category "Tier" "Nope"] })
        NumberValuesNotUniqueElabError.diagnostic?,
      decide (elaborateTemporalValuesNotUniqueSource orderModel ["Order"]
        { first := field "Shipped", rest := [category "Tier" "Nope"] })
        TemporalValuesNotUniqueElabError.diagnostic?].all (· == .mapped .categoryUnknown) := by
  native_decide

/- A carrier that asks no category gate still reads the operand's category first, so
   `FirstFilledValue` refuses an undeclared category with the read's class, alone or repeated, while
   it admits a declared one. The read's position rests on the same source reading as above. -/
example :
    [decide (elaborateFirstFilledTokenSource orderModel ["Order"]
        { first := category "Tier" "Nope", rest := [field "Label"] })
        (fun error => error.diagnostic?),
      decide (elaborateFirstFilledTokenSource orderModel ["Order"]
        { first := category "Tier" "Nope", rest := [category "Tier" "Nope"] })
        (fun error => error.diagnostic?)] =
    [.mapped .categoryUnknown, .mapped .categoryUnknown] := by
  native_decide

private def fillList (computation : Bool) (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) : Decision :=
  decide (if computation then elaborateComputationFieldFillList orderModel ["Order"] ["Order"] { first, rest }
    else elaborateFieldFillList orderModel ["Order"] { first, rest } ["Order"] .quantifier)
    (fun error => match error with | .shape error => error.diagnostic? | _ => none)

example : [false, true].all (fun computation =>
    fillList computation (level "Tier") [field "Label"] == .mapped .categoryNotAllowed &&
    fillList computation (level "Tier") [field "Label", field "Label"] == .mapped .duplicateParam1 &&
    fillList computation (field "Tier") [field "Label"] == .admitted) = true := by native_decide

end A12Kernel.Conformance.EntityListCategoryGate
