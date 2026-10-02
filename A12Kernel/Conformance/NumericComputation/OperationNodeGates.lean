import A12Kernel.Elaboration.NumericComputation.Table

/-! # Number computation operation node-gate locks

Every replayable row of the
[node-gate grids](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates),
measured on the Kernel's static check, through the whole-computation elaborator: the class it reports,
or none for an admitted operation. The model's root `Typ` declares Numbers `N`, `N2` and the target `T`
at scale 2 and `Z` at scale 0, Strings `S` and `S2` and a raw-valued `SR`, a Boolean `B`, a Confirm
`CF`, an unlabelled Enumeration `E` and a labelled `EL`, a DateRange `DR`, and temporal fields whose
component sets the extrema compare: complete Dates `D` and `D3`, a day-optional Date `DP`, a year-month
Date `DM`, a Time `TM`, a Time `TD` declaring a complete date's components, a DateTime `DTT`, and a
Custom `CU`. It unites the grids' three models, which differ only by `Z` and `CU`, and no row reads both.
The grids' bracketed guards and their one `Round` spelling the parser refuses are not replayed.

The rows separate a node's typing from its own authoring gates and both from another node's: a
region's second division answers before an enclosing typing failure (`A03`, `Y14`), a later sibling's
(`c22`) and the target's scale rule (`c01`), and after an earlier sibling's (`c16`, `Y17`, `Y24`). An
exponent's derived scale answers before a power on its left (`c15`, `Y25`), and a call exposes its
largest operand's divisions, not their sum (`c10`, `e2`) and not only its first's (`g1`). A root call is
checked like any operand (`c01`, `c11`), and a lone unsortable leader is refused (`Y03` to `Y12`). The
kind rows lock what the typing walk reads off a declaration: a labelled Enumeration is not string-like
(`B02`, `B03`, `B07`), an extrema call compares component sets rather than kinds (`X10` to `X14`), the
first offending follower decides a chain (`X26`, `X27`), a declaration refused as an operand answers
at its position in the walk (`B21`, `B25`), and a Custom declaration is string-like (`K02`, `K08`).
-/

namespace A12Kernel.Conformance.NumericComputation.OperationNodeGates

open A12Kernel

private def declaration (id : FieldId) (name : String) (kind : FieldKind) : FlatFieldDecl :=
  { id, groupPath := ["Typ"], name, policy := { kind } }

private def targetId : FieldId := 2

private def model : FlatModel :=
  { fields := [
      declaration 0 "N" (.number { scale := 2, signed := true }),
      declaration 1 "N2" (.number { scale := 2, signed := true }),
      declaration targetId "T" (.number { scale := 2, signed := true }),
      declaration 3 "S" .string, declaration 4 "S2" .string, declaration 5 "B" .boolean,
      { declaration 6 "E" .enumeration with enumeration := some { storedTokens := ["1", "2"] } },
      declaration 7 "D" (.temporal .date TemporalComponents.fullDate),
      declaration 8 "TM" (.temporal .time TemporalComponents.time),
      { declaration 9 "EL" .enumeration with
        enumeration := some { storedTokens := ["1", "2"], displayFacts := [
          { locale := "en_US", stored := "1", display := "One" },
          { locale := "en_US", stored := "2", display := "Two" }] } },
      declaration 10 "CF" .confirm,
      { declaration 11 "DR" .dateRange with
        dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } },
      { declaration 12 "SR" .string with
        stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } },
      { declaration 13 "DP" (.temporal .date TemporalComponents.fullDate) with
        temporalTargetPolicy := some { format := "dd.MM.yyyy", partialMode := .dayOptional } },
      declaration 14 "D3" (.temporal .date TemporalComponents.fullDate),
      declaration 15 "DM" (.temporal .date
        { year := true, month := true, day := false, hour := false, minute := false, second := false }),
      declaration 16 "DTT" (.temporal .dateTime TemporalComponents.now),
      declaration 17 "TD" (.temporal .time TemporalComponents.fullDate),
      declaration 18 "Z" (.number { scale := 0, signed := true }),
      { declaration 19 "CU" .string with customType := some { name := "ProjectCode" } }]
    timeZoneId := "Europe/Berlin" }

private abbrev Expr := AuthoredNumericExpr SurfaceNumericAtom

private def f (field : String) : Expr := .atom (.field { base := .relative 0, groups := [], field })
private def lit (value : Nat) : Expr := .literal { value := value, authoredScale := 0 }
private def litd (value : Rat) (scale : Nat) : Expr := .literal { value, authoredScale := scale }
private def add : Expr → Expr → Expr := .binary .add
private def sub : Expr → Expr → Expr := .binary .subtract
private def mul : Expr → Expr → Expr := .binary .multiply
private def dv : Expr → Expr → Expr := .binary .divide
private def pw : Expr → Expr → Expr := .power
private def ab : Expr → Expr := .abs
private def g : Expr → Expr := .group
private def roundDown (body : Expr) : Expr := .round .floor ⟨2, by decide⟩ body

/-- An authored `Max` call over its operands in order. -/
private def mx : List Expr → Expr
  | first :: rest => AuthoredNumericExpr.extremumList .maximum first rest
  | [] => lit 0

/-- An authored `Min` call over its operands in order. -/
private def mn : List Expr → Expr
  | first :: rest => AuthoredNumericExpr.extremumList .minimum first rest
  | [] => lit 0

/-- `[N] / [N2] / [N]`, a region of two divisions. -/
private def twoDivisions : Expr := dv (dv (f "N") (f "N2")) (f "N")

private def filled (field : String) : Option SurfaceComputationCondition :=
  some (.fieldFilled { base := .relative 0, groups := [], field })

/-- The Kernel code the whole computation reports, `none` for an admitted one. -/
private def codeOfAlternatives (alternatives : List (Option SurfaceComputationCondition × Expr)) :
    Option String :=
  match elaborateNumericTargetComputationTableFromSurface model ["Typ"] targetId alternatives with
  | .ok _ => none
  | .error error => some ((error.diagnostic?.map (·.kernelCode)).getD "unprojected")

private def codeOf (expression : Expr) : Option String := codeOfAlternatives [(none, expression)]

/-- The grids' one-operation rows: its id, the operation, and the Kernel's code. -/
private def rows : List (String × Expr × Option String) := [
    ("c01", mx [twoDivisions, f "N2"], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c02", ab twoDivisions, some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c03", add (f "N") (mx [twoDivisions, lit 1]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c04", mx [pw (pw (f "N") (lit 2)) (lit 2), f "N2"], some "MVK_TOO_MANY_POW_FOR_CALC"),
    ("c05", dv (f "N") (ab (dv (f "N2") (f "N"))), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c06", dv (dv (ab (f "N")) (f "N2")) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c07", pw (f "N") (f "N2"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("c08", pw (f "N") (f "Z"), some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("c09", pw (f "N") (litd (3/2) 1), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("c10", mx [dv (f "N") (f "N2"), dv (f "N2") (f "N")], some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("c11", mx [f "N", dv (dv (f "N2") (f "N")) (f "N2")], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c12", dv (dv (f "N") (mx [f "N2", f "N"])) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c14", dv (g (dv (f "N") (f "N2"))) (f "N"), some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("c15", pw (pw (f "N") (lit 2)) (f "N2"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("c16", dv (dv (ab (f "S")) (f "N2")) (f "N"), some "MVK_NO_NUMBER"),
    ("c17", dv (dv (f "N") (f "N2")) (ab (f "S")), some "MVK_NO_NUMBER"),
    ("c18", pw (f "N") (g (pw (lit 2) (lit 2))), some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("c19", mx [twoDivisions, f "S"], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c20", mx [f "S", twoDivisions], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c21", sub (f "S") twoDivisions, some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c22", sub twoDivisions (f "S"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c23", pw (pw (f "N") (f "S")) (lit 2), some "MVK_NO_NUMBER_FOR_CALC"),
    ("c24", pw (pw (f "N") (lit 2)) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("c25", pw (pw (f "S") (lit 2)) (lit 2), some "MVK_NO_NUMBER_FOR_CALC"),
    ("c26", ab (pw (pw (f "N") (lit 2)) (lit 2)), some "MVK_TOO_MANY_POW_FOR_CALC"),
    ("c27", dv (dv (mul (f "N") (f "N2")) (f "N")) (f "N2"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("c28", mx [pw (f "N") (f "N2"), f "N2"], some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("e1", dv (f "N") (mx [dv (f "N2") (f "N"), lit 1]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("e2", ab (mx [dv (f "N") (f "N2"), dv (f "N2") (f "N")]), some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("e3", dv (mx [dv (f "N") (f "N2"), lit 1]) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("e4", dv (f "N") (ab (mx [dv (f "N2") (f "N"), lit 1])), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("e5", mx [dv (mx [dv (f "N") (f "N2"), lit 1]) (f "N"), lit 1], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g1", dv (f "N") (mx [lit 1, dv (f "N2") (f "N")]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g2", dv (f "N") (mx [f "N", f "N", dv (f "N2") (f "N")]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g3", dv (f "N") (mn [dv (f "N2") (f "N"), lit 1]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g4", dv (f "N") (roundDown (dv (f "N2") (f "N"))), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g5", dv (mx [dv (f "N") (f "N2")]) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g6", dv (f "N") (mx [mx [dv (f "N2") (f "N"), lit 1], lit 1]), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g7", dv (roundDown (dv (f "N") (f "N2"))) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("g8", dv (dv (f "N") (mx [lit 1, f "N2"])) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("X01", mx [f "S", f "S2"], some "MVK_NOT_SORTABLE"),
    ("X02", mx [f "E", f "E"], some "MVK_NOT_SORTABLE"),
    ("X03", mx [f "B", f "B"], some "MVK_NOT_SORTABLE"),
    ("X04", mx [f "N", f "N2", f "S"], some "MVK_NOT_SORTABLE"),
    ("X05", mx [f "D", f "D", f "N"], some "MVK_DATE_AND_NONDATE"),
    ("X06", mx [f "N", f "S", f "Nope"], some "MVK_INVALID_ENTITY"),
    ("X07", mx [f "N", f "Nope", f "S"], some "MVK_INVALID_ENTITY"),
    ("X08", mx [mx [f "N", f "S"], f "N2"], some "MVK_NOT_SORTABLE"),
    ("X09", mx [f "D", mx [f "D", f "D"]], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X10", mx [f "D", f "D3"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X11", mx [f "D", f "DM"], some "MVK_DATEFORMATS_NOT_COMPATIBLE"),
    ("X12", mx [f "D", f "DTT"], some "MVK_DATEFORMATS_NOT_COMPATIBLE"),
    ("X13", mx [f "D", f "TD"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X14", mx [f "TD", f "D"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X15", pw (f "S") (f "N"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("X16", pw (lit 2) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("X17", pw (g (add (f "S") (f "S2"))) (lit 2), some "MVK_NO_NUMBER_FOR_CALC"),
    ("X18", add (lit 1) (f "S"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("X19", sub (lit 1) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("X20", mul (lit 2) (f "B"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("X21", ab (mx [f "D", f "D"]), some "MVK_NO_NUMBER"),
    ("X22", add (g (f "S")) (f "N"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("X23", add (mx [f "D", f "D"]) (f "N"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("X24", mn [f "S", f "N", f "D"], some "MVK_NOT_SORTABLE"),
    ("X25", mx [f "N", f "N2", f "D", f "S"], some "MVK_NOT_SORTABLE"),
    ("X26", mx [f "D", f "N", f "TM"], some "MVK_DATE_AND_NONDATE"),
    ("X27", mx [f "D", f "TM", f "N"], some "MVK_DATEFORMATS_NOT_COMPATIBLE"),
    ("X28", ab (g (f "S")), some "MVK_NO_NUMBER"),
    ("X29", mx [f "N"], none),
    ("X30", mx [f "S"], some "MVK_NOT_SORTABLE"),
    ("X31", mx [g (add (f "S") (f "S2")), f "S"], some "MVK_NOT_SORTABLE"),
    ("X32", mn [mx [f "N", f "N2"], f "S"], some "MVK_NOT_SORTABLE"),
    ("X33", f "TD", some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X34", f "DTT", some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X35", mx [f "TM", f "TM"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X36", mx [f "DTT", f "DTT"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("X37", add (mx [f "N", f "N2"]) (mx [f "N", f "S"]), some "MVK_NOT_SORTABLE"),
    ("X38", pw (pw (f "N") (f "N2")) (f "S"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("A01", dv (dv (f "N") (f "N2")) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("A02", dv (dv (f "S") (f "N")) (f "N2"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("A03", add (dv (dv (f "N") (f "N2")) (f "N")) (f "S"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("A04", add (add (f "N") (f "S")) (dv (dv (f "N") (f "N2")) (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("A05", pw (pw (f "N") (lit 2)) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("A06", pw (pw (f "S") (lit 2)) (lit 2), some "MVK_NO_NUMBER_FOR_CALC"),
    ("A07", add (mul (f "N") (f "N2")) (f "S"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("A08", sub (mul (f "N") (f "N2")) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("A09", add (f "S") (mul (f "N") (f "N2")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("A10", add (pw (f "N") (litd (3/2) 1)) (f "S"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("A11", add (f "Nope") (ab (f "S")), some "MVK_INVALID_ENTITY"),
    ("A12", add (add (ab (f "S")) (f "Nope")) (f "T"), some "MVK_NO_NUMBER"),
    ("A22", add (mul (mul (f "N") (f "N2")) (f "N")) (f "S"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("C01", mul (f "N") (f "N2"), some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("C02", dv (dv (f "N") (f "N2")) (f "N"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("C03", pw (f "N") (f "N2"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("C04", pw (f "N") (litd (3/2) 1), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("C05", pw (pw (f "N") (lit 2)) (lit 2), some "MVK_TOO_MANY_POW_FOR_CALC"),
    ("B01", f "EL", some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("B02", add (f "EL") (f "S"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B03", add (f "EL") (f "EL"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B04", sub (f "EL") (f "N"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("B05", ab (f "EL"), some "MVK_NO_NUMBER"),
    ("B06", mx [f "EL", f "N"], some "MVK_NOT_SORTABLE"),
    ("B07", add (f "S") (f "EL"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B08", f "CF", some "MVK_INVALID_COMPARE_TO_YES"),
    ("B09", add (f "CF") (f "N"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B10", add (f "CF") (f "S"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B11", ab (f "CF"), some "MVK_NO_NUMBER"),
    ("B12", mx [f "CF", f "N"], some "MVK_NOT_SORTABLE"),
    ("B13", f "DR", some "MVK_INVALID_COMPARE_TO_DATE_RANGE"),
    ("B14", add (f "DR") (f "N"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B15", sub (f "DR") (f "N"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("B16", add (f "S") (f "DR"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B17", f "SR", some "MVK_INVALID_RAW_TYPE"),
    ("B18", add (f "SR") (f "N"), some "MVK_INVALID_RAW_TYPE"),
    ("B19", add (f "SR") (f "S"), some "MVK_INVALID_RAW_TYPE"),
    ("B20", add (f "N") (f "SR"), some "MVK_INVALID_RAW_TYPE"),
    ("B21", sub (g (add (f "N") (f "S"))) (f "SR"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B22", f "DP", some "MVK_INVALID_DATE_TYPE"),
    ("B23", add (f "DP") (f "N"), some "MVK_INVALID_DATE_TYPE"),
    ("B24", add (f "N") (f "DP"), some "MVK_INVALID_DATE_TYPE"),
    ("B25", sub (g (add (f "N") (f "S"))) (f "DP"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("B26", mx [f "DP", f "D"], some "MVK_INVALID_DATE_TYPE"),
    ("B27", ab (f "DR"), some "MVK_NO_NUMBER"),
    ("B28", mx [f "DR", f "N"], some "MVK_NOT_SORTABLE"),
    ("B29", sub (f "CF") (f "N"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("B30", add (f "EL") (lit 1), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Y01", mx [f "S", f "Nope"], some "MVK_INVALID_ENTITY"),
    ("Y02", mx [f "D", f "Nope"], some "MVK_INVALID_ENTITY"),
    ("Y03", mx [f "B"], some "MVK_NOT_SORTABLE"),
    ("Y04", mx [f "E"], some "MVK_NOT_SORTABLE"),
    ("Y05", mx [f "D"], some "MVK_INVALID_COMPARE_TO_DATE"),
    ("Y06", mx [f "EL"], some "MVK_NOT_SORTABLE"),
    ("Y07", mx [f "CF"], some "MVK_NOT_SORTABLE"),
    ("Y08", mx [f "DR"], some "MVK_NOT_SORTABLE"),
    ("Y09", mn [f "S"], some "MVK_NOT_SORTABLE"),
    ("Y10", mx [f "S", f "Nope", f "N"], some "MVK_INVALID_ENTITY"),
    ("Y11", mx [f "B", f "Nope"], some "MVK_INVALID_ENTITY"),
    ("Y12", mx [g (add (f "S") (f "S2"))], some "MVK_NOT_SORTABLE"),
    ("Y13", add (pw (pw (f "N") (lit 2)) (lit 2)) (f "S"), some "MVK_TOO_MANY_POW_FOR_CALC"),
    ("Y14", add (g (dv (dv (f "N") (f "N2")) (f "N"))) (f "S"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("Y15", sub (dv (dv (f "N") (f "N2")) (f "N")) (ab (f "S")), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("Y16", add (pw (f "N") (f "N2")) (f "S"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("Y17", add (add (f "N") (f "S")) (pw (f "N") (f "N2")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Y18", add (ab (dv (dv (f "N") (f "N2")) (f "N"))) (f "S"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("Y19", mx [dv (dv (f "N") (f "N2")) (f "N"), f "S"], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("Y20", add (f "S") (g (dv (dv (f "N") (f "N2")) (f "N"))), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("Y21", pw (pw (f "N") (f "S")) (lit 2), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Y22", sub (g (pw (f "N") (litd (3/2) 1))) (f "S"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("Y23", mul (mul (f "N") (f "N2")) (f "S"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Y24", dv (dv (f "N") (f "S")) (f "N2"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Y25", pw (pw (f "N") (lit 2)) (f "N2"), some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("Y26", mx [f "N", pw (f "N2") (litd (3/2) 1), f "S"], some "MVK_INVALID_NUMBER_FOR_EXP"),
    ("Y27", dv (dv (dv (f "N") (f "N2")) (f "N")) (f "S"), some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("K01", f "CU", some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("K02", add (f "CU") (f "S"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("K03", add (f "S") (f "CU"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("K04", add (f "CU") (f "N"), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("K05", sub (f "CU") (f "N"), some "MVK_NO_NUMBER_FOR_CALC"),
    ("K06", ab (f "CU"), some "MVK_NO_NUMBER"),
    ("K07", mx [f "CU", f "N"], some "MVK_NOT_SORTABLE"),
    ("K08", add (f "CU") (f "CU"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("K09", add (f "CU") (f "E"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING")]

/- Every row reports the Kernel's code; the failing ids are listed, so a mismatch names its row. -/
example : (rows.filter fun (_, expression, expected) => codeOf expression != expected).map (·.1) =
    [] := by
  native_decide

/-- The rows of two guarded alternatives: each alternative's gates answer in authored order, ahead of
any read of the target, and a guard's name class ahead of its operation's. -/
private def alternativeRows : List (String × List (Option SurfaceComputationCondition × Expr) × Option String) := [
    ("G01", [(filled "N", mul (f "N") (f "N2")), (filled "N2", add (f "N") (f "S"))], some "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("G02", [(filled "N", add (f "N") (f "S")), (filled "N2", mul (f "N") (f "N2"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G03", [(filled "N", add (f "T") (lit 1)), (filled "N2", add (f "N") (f "S"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G04", [(filled "T", add (f "N") (lit 1)), (filled "N2", add (f "N") (f "S"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G05", [(none, add (f "N") (lit 1)), (filled "N2", add (f "N") (f "S"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G06", [(filled "N", add (f "N") (f "Nope")), (filled "N2", add (f "N") (f "S"))], some "MVK_INVALID_ENTITY"),
    ("G07", [(filled "N", dv (dv (f "N") (f "N2")) (f "N")), (filled "N2", add (f "N") (f "S"))], some "MVK_TOO_MANY_DIV_FOR_CALC"),
    ("G08", [(filled "Nope", add (f "N") (lit 1)), (filled "N2", add (f "N") (f "S"))], some "MVK_INVALID_ENTITY"),
    ("G09", [(filled "N", add (f "N") (f "S")), (filled "Nope", add (f "N") (lit 1))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G10", [(filled "N", add (f "N") (lit 1)), (filled "N2", add (f "N") (f "S"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G11", [(filled "N", add (f "N") (f "S")), (none, add (f "N") (lit 1))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("G12", [(filled "N", add (f "N") (lit 1)), (filled "N2", add (f "T") (f "S"))], some "MVK_NO_STRING_OR_NUMBER_FOR_ADD")]

example : (alternativeRows.filter fun (_, alternatives, expected) =>
    codeOfAlternatives alternatives != expected).map (·.1) = [] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.OperationNodeGates
