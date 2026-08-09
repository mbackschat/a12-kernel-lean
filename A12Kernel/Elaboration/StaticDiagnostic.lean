/-! # Kernel static-legality diagnostic classes

The Kernel reports an illegal model as a named diagnostic, and **which** name it reports is observable behavior, not an implementation detail. Two illegal models that both fail authoring are still distinguishable if they report different classes, and three consumer profiles depend on that distinction: an importer must decide whether a rejected model is repairable, a rule-refactoring tool must preserve the class its transformation would trigger, and an Explain consumer must name the actual failure.

This vocabulary is therefore part of the semantic account rather than an error-message convenience. It grows one family at a time, and it deliberately admits **no** class this project has not established, so a family's uncovered refusals stay visibly uncovered instead of being mapped to a plausible-looking name. A local refusal with no established class projects to `none`, which is the honest state and a countable coverage measure.

Distinguish this from `A12Kernel.Reference.Support.DiagnosticCode`, which is the public reference process's own transport-level rejection surface (bad JSON, unsupported version, resource limit). That vocabulary describes *this project's* protocol boundary; this one describes the *Kernel's* model check.

Scope: the codes below cover the established field-list operand-admission and fixed filled-group computation-admission families. Coverage, per-mapping evidence status, and remaining families belong to [`IMPLEMENTATION-MAP.md`](../../docs/IMPLEMENTATION-MAP.md); [`SEMANTICS-GAPS.md`](../../docs/SEMANTICS-GAPS.md) owns the open axis.
-/

namespace A12Kernel

/-- One Kernel model-check diagnostic class this project has established. The constructor names are local; `kernelCode` carries the exact `MVK_` identity a consumer compares against. -/
inductive KernelStaticDiagnostic where
  /-- An operand kind the operator refuses outright, or a temporal operand list whose declared formats disagree. Both report this one code. -/
  | onlyStringEnumNumberDateAllowed
  /-- Operands drawn from two different comparability categories, each individually admissible. -/
  | varyingTypesNotAllowed
  /-- An operand list below the operator's required arity. -/
  | paramSizeInvalidN
  /-- A fixed filled-group count has fewer than two operands. -/
  | paramSizeInvalidGN
  /-- The exact same group operand occurs more than once. -/
  | duplicateParam1
  /-- Two group operands overlap by ancestor and descendant. -/
  | duplicateParam2
  /-- A repeatable group was supplied without its required star address. -/
  | noWildcard
  deriving Repr, DecidableEq

namespace KernelStaticDiagnostic

/-- The exact Kernel diagnostic identifier. This string is the observable, so it is never derived from the constructor name. -/
def kernelCode : KernelStaticDiagnostic → String
  | .onlyStringEnumNumberDateAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"
  | .varyingTypesNotAllowed => "MVK_VARYING_TYPES_NOT_ALLOWED"
  | .paramSizeInvalidN => "MVK_PARAMSIZE_INVALIDN"
  | .paramSizeInvalidGN => "MVK_PARAMSIZE_INVALIDGN"
  | .duplicateParam1 => "MVK_DUPLICATE_PARAM1"
  | .duplicateParam2 => "MVK_DUPLICATE_PARAM2"
  | .noWildcard => "MVK_NO_WILDCARD"

/-- Every established class, so a consumer can enumerate the covered surface and a law can quantify over it. -/
def all : List KernelStaticDiagnostic :=
  [.onlyStringEnumNumberDateAllowed, .varyingTypesNotAllowed, .paramSizeInvalidN,
    .paramSizeInvalidGN, .duplicateParam1, .duplicateParam2, .noWildcard]

end KernelStaticDiagnostic

end A12Kernel
