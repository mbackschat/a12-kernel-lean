import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.CheckedStarDocument

/-! # Numeric aggregate elaboration conformance support -/

namespace A12Kernel.Conformance.NumericAggregateElaboration.Support

open A12Kernel

def unsignedA : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "UnsignedA",
    policy := { kind := .number { scale := 0, signed := false } } }

def signedB : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "SignedB",
    policy := { kind := .number { scale := 0, signed := true } } }

def unsignedC : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "UnsignedC",
    policy := { kind := .number { scale := 0, signed := false } } }

def text : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Text",
    policy := { kind := .string } }

def repeated : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

def repeatedPrice : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Rows"], name := "Price",
    policy := { kind := .number { scale := 2, signed := true } },
    repeatableScope := [10] }

def repeatedText : FlatFieldDecl :=
  { id := 6, groupPath := ["Form", "Rows"], name := "Label",
    policy := { kind := .string }, repeatableScope := [10] }

def otherRepeated : FlatFieldDecl :=
  { id := 7, groupPath := ["Form", "Other"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [20] }

def nestedRepeated : FlatFieldDecl :=
  { id := 8, groupPath := ["Form", "Rows", "Details"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10, 30] }

def filterLeft : FlatFieldDecl :=
  { id := 9, groupPath := ["Form", "Rows"], name := "FilterLeft",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

def filterRight : FlatFieldDecl :=
  { id := 10, groupPath := ["Form", "Rows"], name := "FilterRight",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

def rows : RepeatableGroupDecl :=
  { level := 10, path := ["Form", "Rows"], repeatability := some 3 }

def otherRows : RepeatableGroupDecl :=
  { level := 20, path := ["Form", "Other"], repeatability := some 3 }

def detailRows : RepeatableGroupDecl :=
  { level := 30, path := ["Form", "Rows", "Details"], repeatability := some 2 }

def model : FlatModel :=
  { fields := [unsignedA, signedB, unsignedC, text, repeated, filterLeft,
      filterRight]
    repeatableGroups := [rows] }

def productModel : FlatModel :=
  { fields := model.fields ++ [repeatedPrice, repeatedText, otherRepeated,
      nestedRepeated]
    repeatableGroups := [rows, otherRows, detailRows] }

def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

def sum (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath) : SurfaceNumericAggregateFields :=
  { first, rest }

def raw (a b c : RawCell) : RawFlatContext where
  read field :=
    if field = unsignedA.id then a
    else if field = signedB.id then b
    else if field = unsignedC.id then c
    else .empty

def operandOf (authored : SurfaceNumericAggregateFields)
    (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateSum input)

def extremumOperandOf (op : NumericExtremumOp)
    (authored : SurfaceNumericAggregateFields) (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateExtremum op input)

def errorOf (authored : SurfaceNumericAggregateFields) : Option NumericAggregateElabError :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

def tenPow50 : Rat := 10 ^ 50

def starredAmount : SurfaceSingleStarFieldPath :=
  { base := .absolute
    groupsBeforeStar := ["Form"]
    starredGroup := "Rows"
    field := "Amount" }

def repeatedRaw (candidates : List RowIndex) (a b c : RawCell) :
    RawSingleGroupContext where
  candidates := candidates
  read row field :=
    if field != repeated.id then .empty
    else match row with
      | 1 => a
      | 2 => b
      | 3 => c
      | _ => .empty

def starElabErrorOf (source : SurfaceSingleStarFieldPath)
    (targetModel : FlatModel := model) : Option NumericStarElabError :=
  match elaborateNumericStarSource targetModel ["Form"] source with
  | .ok _ => none
  | .error error => some error

def starSumOf (raw : RawSingleGroupContext) : Option NumericOperand :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateSum raw with
      | .ok operand => some operand
      | .error _ => none

def starExtremumOf (op : NumericExtremumOp) (raw : RawSingleGroupContext) :
    Option NumericOperand :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateExtremum op raw with
      | .ok operand => some operand
      | .error _ => none

def starContextErrorOf (raw : RawSingleGroupContext) :
    Option NumericStarContextError :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateSum raw with
      | .ok _ => none
      | .error error => some error

def starFirstFilledOf (raw : RawSingleGroupContext) :
    Option FirstFilledNumberResult :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateFirstFilled raw with
      | .ok result => some result
      | .error _ => none

def aggregateStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true }]
    field := "Amount" }

def productStar (field : String) (group : String := "Rows") :
    SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := group, starred := true }]
    field }

def nestedProductStar (outerStar : Bool) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := outerStar },
      { name := "Details", starred := true }]
    field := "Amount" }

def productSource (left right : SurfaceStarFieldPath) :
    SurfaceNumericProductAggregate :=
  { left, right }

def productErrorOf (left right : SurfaceStarFieldPath) :
    Option NumericProductAggregateElabError :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource left right) with
  | .ok _ => none
  | .error error => some error

def productRead (left right : RowIndex → RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  match environment with
  | [(10, row)] =>
      if field == repeated.id then left row
      else if field == repeatedPrice.id then right row
      else .empty
  | _ => .empty

def productDocument (selectedRows : List RowIndex) : Document :=
  { instantiatedRows := selectedRows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

def productValidationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) : Option NumericOperand :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateValidation (productDocument selectedRows) []
        (productRead left right)).toOption

def productCheckedRead (left right : RowIndex → RawCell)
    (requiredLeft : Bool) (environment : Env) (field : FieldId) : CheckedCell :=
  let raw := productRead left right environment field
  if field == repeated.id then
    let cell := repeated.checkRaw raw
    if requiredLeft && raw == .presentEmpty then
      { cell with findings := [.required] }
    else
      cell
  else if field == repeatedPrice.id then
    repeatedPrice.checkRaw raw
  else
    malformedCheckedCell

def productCheckedValidationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (requiredLeft : Bool := false) :
    Option NumericOperand :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateAt .validation (productDocument selectedRows) []
        (productCheckedRead left right requiredLeft)).toOption

def productComputationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (requiredLeft : Bool := false) :
    Option NumericComputationResult :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateComputation (productDocument selectedRows) []
        (productCheckedRead left right requiredLeft)).toOption

def productPartialOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (scope : ValidationRelevanceScope) :
    Option PartialValidationNumberAggregateResult :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluatePartial (productDocument selectedRows) [] scope
        (productRead left right)).toOption

def productScale : Option NumericScaleSummary :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked => some checked.scaleSummary

def cells3 (first second third : RawCell) : RowIndex → RawCell
  | 1 => first
  | 2 => second
  | 3 => third
  | _ => .empty

def productRelevance (path : List String)
    (indices : List RelevanceIndex) : RelevantEntityPattern :=
  { path, indices }

end A12Kernel.Conformance.NumericAggregateElaboration.Support
