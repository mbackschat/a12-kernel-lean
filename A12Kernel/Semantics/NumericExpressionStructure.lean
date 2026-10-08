import A12Kernel.Semantics.NumericExpression

namespace A12Kernel.AuthoredNumericExpr

/-- Retain subterm bounds while printing mutually recursive numeric/temporal operands. -/
def formatWithSubterm [SizeOf Atom] (expression : AuthoredNumericExpr Atom)
    (formatAtom : (atom : Atom) → sizeOf atom < sizeOf expression → Std.Format) : Std.Format :=
  match expression with
  | .atom sourceAtom => formatAtom sourceAtom (by simp)
  | .literal value => repr value
  | .group body => "group (" ++ Std.Format.joinSep [formatWithSubterm body (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .abs body => "abs (" ++ Std.Format.joinSep [formatWithSubterm body (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .extremumCall op body => "extremumCall (" ++ Std.Format.joinSep [repr op, formatWithSubterm body (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .round mode places body => "round (" ++ Std.Format.joinSep [repr mode, repr places, formatWithSubterm body (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .binary op left right => "binary (" ++ Std.Format.joinSep [repr op, formatWithSubterm left (fun atom h => formatAtom atom (by simp_all; omega)), formatWithSubterm right (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .power base exponent => "power (" ++ Std.Format.joinSep [formatWithSubterm base (fun atom h => formatAtom atom (by simp_all; omega)), formatWithSubterm exponent (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"
  | .extremum op left right => "extremum (" ++ Std.Format.joinSep [repr op, formatWithSubterm left (fun atom h => formatAtom atom (by simp_all; omega)), formatWithSubterm right (fun atom h => formatAtom atom (by simp_all; omega))] ") (" ++ ")"

/-- Structural equality supplies strict atom bounds to an enclosing recursive family. -/
def decideEqWithSubterm [SizeOf Atom] (left right : AuthoredNumericExpr Atom)
    (equalAtom : (a b : Atom) → sizeOf a < sizeOf left → sizeOf b < sizeOf right → Decidable (a = b)) :
    Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case atom.atom a b =>
    letI := equalAtom a b (by simp) (by simp)
    exact decidable_of_iff (a = b) (by simp)
  case literal.literal a b => exact decidable_of_iff (a = b) (by simp)
  case group.group body nextBody =>
    letI := decideEqWithSubterm body nextBody (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (body = nextBody) (by simp)
  case abs.abs body nextBody =>
    letI := decideEqWithSubterm body nextBody (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (body = nextBody) (by simp)
  case extremumCall.extremumCall op body nextOp nextBody =>
    letI := decideEqWithSubterm body nextBody (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (op = nextOp ∧ body = nextBody) (by simp)
  case round.round mode places body nextMode nextPlaces nextBody =>
    letI := decideEqWithSubterm body nextBody (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (mode = nextMode ∧ places = nextPlaces ∧ body = nextBody) (by simp)
  case binary.binary op left right nextOp nextLeft nextRight =>
    letI := decideEqWithSubterm left nextLeft (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    letI := decideEqWithSubterm right nextRight (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (op = nextOp ∧ left = nextLeft ∧ right = nextRight) (by simp)
  case power.power base exponent nextBase nextExponent =>
    letI := decideEqWithSubterm base nextBase (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    letI := decideEqWithSubterm exponent nextExponent (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (base = nextBase ∧ exponent = nextExponent) (by simp)
  case extremum.extremum op left right nextOp nextLeft nextRight =>
    letI := decideEqWithSubterm left nextLeft (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    letI := decideEqWithSubterm right nextRight (fun a b ha hb => equalAtom a b (by simp_all; omega) (by simp_all; omega))
    exact decidable_of_iff (op = nextOp ∧ left = nextLeft ∧ right = nextRight) (by simp)

/-- Ordered occurrence traversal retains strict bounds for recursive metadata consumers. -/
def flatMapAtomsSubterm [SizeOf Atom] (expression : AuthoredNumericExpr Atom)
    (visit : (source : Atom) → sizeOf source < sizeOf expression → List Result) : List Result :=
  match expression with
  | .atom source => visit source (by simp)
  | .literal _ => []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      body.flatMapAtomsSubterm fun source h => visit source (by simp_all; omega)
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.flatMapAtomsSubterm (fun source h => visit source (by simp_all; omega)) ++
        right.flatMapAtomsSubterm (fun source h => visit source (by simp_all; omega))

end A12Kernel.AuthoredNumericExpr
