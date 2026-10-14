import A12Kernel.Elaboration.NumericComputation.Core

/-! # Structural preflight of numeric computation atoms

The first structural fault of a lowered or checked computation operation, decided before any
context read so that data-dependent poison cannot hide it.
-/

namespace A12Kernel

def FlatFieldDecl.numericComputationFault?
    (declaration : FlatFieldDecl) : Option NumericComputationFault :=
  if declaration.toNumberField?.isSome then
    none
  else
    some (.fieldKindMismatch declaration.id)

/-- Preflight one resolved source atom. Checked temporal component atoms already retain their kind, while a forged direct declaration can still carry a non-Number kind. -/
def NumericComputationAtom.numericComputationFault? :
    ResolvedNumericAtom FlatFieldDecl Aggregate →
      Option NumericComputationFault
  | .field declaration => declaration.numericComputationFault?
  | .baseYear _ => none
  | .fixedCurrentRepetition _ => none
  | .boundCurrentRepetition _ => none
  | .baseYearDatePart _ _ _ => none
  | .temporalFieldPart _ _ _ => none
  | .dateRangeBoundPart _ _ _ => none
  | .stringLength _ => none
  | .stringRange _ _ _ => none
  | .fieldValueAsNumber _ => none
  -- Each difference arm preflights through the SAME predicate its checked owner gates with, rather
  -- than restating the rule, so the two cannot drift. All three previously tested the declared
  -- kind, which is not what the Kernel reads: the declared format is
  -- ([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
  -- `hasBaseYear` is unavailable on this model-free route, so the completed-period arm passes the
  -- permissive value; a preflight must never be stricter than the gate it guards.
  | .dateDifference unit left right =>
      let fault? : ResolvedDateDifferenceOperand → Option NumericComputationFault
        | .field source =>
            if unit.admittedBy true source.components then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ | .literal _ _ | .today _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .dateTimeDifference unit left right =>
      let fault? : FlatTemporalOperand → Option NumericComputationFault
        | .fieldValue source =>
            if unit.admittedBy source.components then none
            else some (.fieldKindMismatch source.id)
        | .nowValue => none
        | _ => some .unsupportedDateTimeDifferenceOperand
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .dayDifference _ left right =>
      let fault? : ResolvedDateDifferenceOperand FlatTemporalField true → Option NumericComputationFault
        | .field source =>
            if CalendarDayDifference.admittedBy source.components then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ | .literal _ _ | .today _ | .now _ _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .aggregate _ _ => none
  -- No model is available on this route, so no single operand can be named.
  | .filledGroupCount _ => some .groupCountNeedsModel

/-- The structural fault a fixed group-count operand carries, if any.

    Shared by both group-count atoms so the pre-read gate cannot end up narrower than the reader
    on one of them; `readGroupCountOperand_fixed_error_iff_notAdmitted` ties it to the reader. -/
def fixedGroupCountOperandFault? (model : FlatModel) (reference : ResolvedGroupReference) :
    Option NumericComputationFault :=
  if reference.computationOperandAdmitted model then none
  else some (.unsupportedGroupCount reference.path)

def CheckedNumericComputationAtom.numericComputationFault? :
    CheckedNumericComputationAtom model → Option NumericComputationFault
  | .filledFieldCount source => source.operands.findSome? fun operand =>
      match operand with
      | .indexed _ | .keyed _ => none
      | operand => if operand.hasHaving then none else
        match CheckedFieldFillList.computationSources { operands := [operand] } with
        | .ok _ => none
        | .error error => some (.fieldFillSource error)
  | .indexed _ | .indexedString _ | .temporalExpression _ | .firstFilled _ => none
  | .valueCount _ _ => none
  | .tokenDistinctCount _ | .temporalDistinctCount _ => none
  | .tokenValueCount _ => none
  | .booleanValueCount _ => none
  -- A group operand's boundary is model-structural, so it is decided here rather than left
  -- to the reading branch, where a data-dependent poison could otherwise hide it: `evalOrdered`
  -- stops at a left poison, so an ungated atom's structural fault is never reached. It must be the
  -- reader's own admission and not a narrower copy: refusing here what the reader would count
  -- makes the gate, rather than the operand, decide the answer.
  | .numeric (.filledGroupCount groups) =>
      groups.findSome? (fixedGroupCountOperandFault? model)
  | .numeric source =>
      NumericComputationAtom.numericComputationFault? source
  | .sumOfProducts _ => none
  -- The same gate, because this atom holds the same `fixed` operand form. Only the fixed operands
  -- are pre-decided: a starred operand's refusal is a `StarAddressingError` over the document's
  -- own row topology, which no model-structural pass can answer.
  | .filledGroupCountMixed operands =>
      operands.findSome? fun operand =>
        match operand with
        | .fixed reference => fixedGroupCountOperandFault? model reference
        | .starred _ => none
        | .starredPresence _ => none

namespace LoweredNumericExpr

/-- The first structural fault in the complete lowered tree. This pass runs before any context read, so a bad atom cannot be hidden by data-dependent poison. -/
def computationFaultWith?
    (fault? : Atom → Option NumericComputationFault) :
    LoweredNumericExpr Atom → Option NumericComputationFault
  | .atom sourceAtom => fault? sourceAtom
  | .literal _ => none
  | .binary _ left right | .power left right | .extremum _ left right =>
      match left.computationFaultWith? fault? with
      | some fault => some fault
      | none => right.computationFaultWith? fault?
  | .abs body | .extremumCall _ _ body => body.computationFaultWith? fault?
  | .round _ _ body => body.computationFaultWith? fault?

def computationFault? (expression : LoweredNumericExpr FlatFieldDecl) :
    Option NumericComputationFault :=
  expression.computationFaultWith? FlatFieldDecl.numericComputationFault?

end LoweredNumericExpr

end A12Kernel
