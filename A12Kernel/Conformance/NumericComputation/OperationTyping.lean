import A12Kernel.Elaboration.NumericComputation.Table

/-! # Number computation operation typing locks

Every replayable row of the
[operation-typing grid](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-typing),
measured on the Kernel's static check, through the whole-computation elaborator: the class it reports,
or none for an admitted operation. The model declares two Numbers and a Number target at scale 2, two
Strings, a Boolean, an unlabelled Enumeration, a Date and a Time. The grid's parenthesised rows, its
String literals and its `Round` row are a parser's refusals or surfaces this tree does not carry, and
are not replayed.

The rows separate a per-atom class from the operator's typing (one String under `+`, `-` and `Abs`
draws three classes), a refused pair from a concatenation (two Strings add), the leader of an extrema
call from its offender, and the post-order walk from a leaf-first one: an inner node's class answers
before a later operand's read and before the target's.
-/

namespace A12Kernel.Conformance.NumericComputation.OperationTyping

open A12Kernel

private def declaration (id : FieldId) (name : String) (kind : FieldKind) :
    FlatFieldDecl :=
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
      declaration 8 "TM" (.temporal .time
        { year := false, month := false, day := false, hour := true, minute := true, second := true })]
    timeZoneId := "Europe/Berlin" }

private def f (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .relative 0, groups := [], field })

private def lit (value : Nat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value := value, authoredScale := 0 }

/-- The Kernel code the whole computation reports, `none` for an admitted one. -/
private def codeOf (expression : AuthoredNumericExpr SurfaceNumericAtom) : Option String :=
  match elaborateNumericTargetComputationTable model ["Typ"] targetId [(none, expression)] with
  | .ok _ => none
  | .error error => some ((error.diagnostic?.map (·.kernelCode)).getD "unprojected")

/-- The grid's rows: its id, the operation, and the Kernel's code. -/
private def rows : List (String × AuthoredNumericExpr SurfaceNumericAtom × Option String) := [
    ("Saddr", (.binary .add (f "N") (f "S")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Saddl", (.binary .add (f "S") (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Ssubr", (.binary .subtract (f "N") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Ssubl", (.binary .subtract (f "S") (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Smul", (.binary .multiply (f "N") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Sdiv", (.binary .divide (f "N") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Spow", (.power (f "N") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Sbare", (f "S"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("Sabs", (.abs (f "S")), some "MVK_NO_NUMBER"),
    ("Smaxr", (.extremumCall .maximum (.extremum .maximum (f "N") (f "S"))), some "MVK_NOT_SORTABLE"),
    ("Smaxl", (.extremumCall .maximum (.extremum .maximum (f "S") (f "N"))), some "MVK_NOT_SORTABLE"),
    ("Smin", (.extremumCall .minimum (.extremum .minimum (f "N") (f "S"))), some "MVK_NOT_SORTABLE"),
    ("Sabsadd", (.abs (.binary .add (f "N") (f "S"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Smaxadd", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "S")) (lit 1))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Saddlit", (.binary .add (f "S") (lit 1)), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Baddr", (.binary .add (f "N") (f "B")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Baddl", (.binary .add (f "B") (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Bsubr", (.binary .subtract (f "N") (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Bsubl", (.binary .subtract (f "B") (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Bmul", (.binary .multiply (f "N") (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Bdiv", (.binary .divide (f "N") (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Bpow", (.power (f "N") (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Bbare", (f "B"), some "MVK_INVALID_COMPARE_TO_YESNO"),
    ("Babs", (.abs (f "B")), some "MVK_NO_NUMBER"),
    ("Bmaxr", (.extremumCall .maximum (.extremum .maximum (f "N") (f "B"))), some "MVK_NOT_SORTABLE"),
    ("Bmaxl", (.extremumCall .maximum (.extremum .maximum (f "B") (f "N"))), some "MVK_NOT_SORTABLE"),
    ("Bmin", (.extremumCall .minimum (.extremum .minimum (f "N") (f "B"))), some "MVK_NOT_SORTABLE"),
    ("Babsadd", (.abs (.binary .add (f "N") (f "B"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Bmaxadd", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "B")) (lit 1))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Baddlit", (.binary .add (f "B") (lit 1)), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Eaddr", (.binary .add (f "N") (f "E")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Eaddl", (.binary .add (f "E") (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Esubr", (.binary .subtract (f "N") (f "E")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Esubl", (.binary .subtract (f "E") (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Emul", (.binary .multiply (f "N") (f "E")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Ediv", (.binary .divide (f "N") (f "E")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Epow", (.power (f "N") (f "E")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Ebare", (f "E"), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("Eabs", (.abs (f "E")), some "MVK_NO_NUMBER"),
    ("Emaxr", (.extremumCall .maximum (.extremum .maximum (f "N") (f "E"))), some "MVK_NOT_SORTABLE"),
    ("Emaxl", (.extremumCall .maximum (.extremum .maximum (f "E") (f "N"))), some "MVK_NOT_SORTABLE"),
    ("Emin", (.extremumCall .minimum (.extremum .minimum (f "N") (f "E"))), some "MVK_NOT_SORTABLE"),
    ("Eabsadd", (.abs (.binary .add (f "N") (f "E"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Emaxadd", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "E")) (lit 1))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Eaddlit", (.binary .add (f "E") (lit 1)), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Daddr", (.binary .add (f "N") (f "D")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Daddl", (.binary .add (f "D") (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Dsubr", (.binary .subtract (f "N") (f "D")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Dsubl", (.binary .subtract (f "D") (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Dmul", (.binary .multiply (f "N") (f "D")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Ddiv", (.binary .divide (f "N") (f "D")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Dpow", (.power (f "N") (f "D")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Dbare", (f "D"), some "MVK_INVALID_COMPARE_TO_DATE"),
    ("Dabs", (.abs (f "D")), some "MVK_NO_NUMBER"),
    ("Dmaxr", (.extremumCall .maximum (.extremum .maximum (f "N") (f "D"))), some "MVK_NOT_SORTABLE"),
    ("Dmaxl", (.extremumCall .maximum (.extremum .maximum (f "D") (f "N"))), some "MVK_DATE_AND_NONDATE"),
    ("Dmin", (.extremumCall .minimum (.extremum .minimum (f "N") (f "D"))), some "MVK_NOT_SORTABLE"),
    ("Dabsadd", (.abs (.binary .add (f "N") (f "D"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Dmaxadd", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "D")) (lit 1))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Daddlit", (.binary .add (f "D") (lit 1)), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("TMaddr", (.binary .add (f "N") (f "TM")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("TMaddl", (.binary .add (f "TM") (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("TMsubr", (.binary .subtract (f "N") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("TMsubl", (.binary .subtract (f "TM") (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("TMmul", (.binary .multiply (f "N") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("TMdiv", (.binary .divide (f "N") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("TMpow", (.power (f "N") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("TMbare", (f "TM"), some "MVK_INVALID_COMPARE_TO_DATE"),
    ("TMabs", (.abs (f "TM")), some "MVK_NO_NUMBER"),
    ("TMmaxr", (.extremumCall .maximum (.extremum .maximum (f "N") (f "TM"))), some "MVK_NOT_SORTABLE"),
    ("TMmaxl", (.extremumCall .maximum (.extremum .maximum (f "TM") (f "N"))), some "MVK_DATE_AND_NONDATE"),
    ("TMmin", (.extremumCall .minimum (.extremum .minimum (f "N") (f "TM"))), some "MVK_NOT_SORTABLE"),
    ("TMabsadd", (.abs (.binary .add (f "N") (f "TM"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("TMmaxadd", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "TM")) (lit 1))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("TMaddlit", (.binary .add (f "TM") (lit 1)), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("PSS2add", (.binary .add (f "S") (f "S2")), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("PSS2sub", (.binary .subtract (f "S") (f "S2")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("PSBadd", (.binary .add (f "S") (f "B")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("PSBsub", (.binary .subtract (f "S") (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("PDSadd", (.binary .add (f "D") (f "S")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("PDSsub", (.binary .subtract (f "D") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("PBEadd", (.binary .add (f "B") (f "E")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("PBEsub", (.binary .subtract (f "B") (f "E")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("PDTMadd", (.binary .add (f "D") (f "TM")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("PDTMsub", (.binary .subtract (f "D") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Cctl", (.binary .add (f "N") (f "N2")), none),
    ("Q07", (.binary .subtract (.binary .add (f "N") (f "S")) (f "N2")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q08", (.binary .subtract (.binary .add (f "S") (f "S2")) (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q09", (.binary .add (.binary .add (f "S") (f "S2")) (f "N")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q10", (.binary .add (.binary .add (f "N") (f "S")) (f "S2")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q11", (.abs (.binary .add (f "S") (f "S2"))), some "MVK_NO_NUMBER"),
    ("Q12", (.binary .add (f "E") (f "E")), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("Q13", (.binary .add (f "S") (f "E")), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("Q14", (.binary .add (f "E") (f "S")), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("Q15", (.binary .add (f "D") (f "D")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q16", (.binary .subtract (f "D") (f "D")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q17", (.binary .subtract (f "TM") (f "TM")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q18", (.binary .add (f "B") (f "B")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q19", (.binary .add (f "N") (.binary .multiply (f "S") (f "N2"))), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q20", (.binary .add (.binary .multiply (f "S") (f "N")) (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q21", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "S") (f "S2")) (f "N"))), some "MVK_NOT_SORTABLE"),
    ("Q22", (.abs (.binary .subtract (f "N") (f "S"))), some "MVK_NO_NUMBER_FOR_CALC"),
    ("Q26", (.extremumCall .maximum (.extremum .maximum (f "N") (.binary .add (f "N2") (f "S")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q27", (.extremumCall .maximum (.extremum .maximum (.binary .add (f "N") (f "S")) (f "D"))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("Q28", (.binary .add (.abs (f "S")) (f "N")), some "MVK_NO_NUMBER"),
    ("Q29", (.binary .subtract (f "N") (.abs (f "S"))), some "MVK_NO_NUMBER"),
    ("Q30", (.binary .add (.binary .subtract (f "S") (f "N")) (f "B")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("R01", (.binary .multiply (.group (.binary .add (f "N") (f "N2"))) (lit 2)), none),
    ("R02", (.binary .subtract (.group (.binary .add (f "N") (f "S"))) (.group (.binary .multiply (f "N") (f "B")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("R03", (.binary .subtract (.group (.binary .multiply (f "N") (f "B"))) (.group (.binary .add (f "N") (f "S")))), some "MVK_NO_NUMBER_FOR_CALC"),
    ("R04", (.binary .multiply (f "N") (.group (.binary .add (f "N2") (f "S")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("R05", (.binary .multiply (.group (.binary .add (f "S") (f "S2"))) (f "N")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("R06", (.binary .multiply (.group (.binary .add (f "N") (f "S"))) (.group (.binary .add (f "S") (f "S2")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("R07", (.binary .add (.group (.binary .add (f "S") (f "S2"))) (.group (.binary .add (f "N") (f "N2")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("R08", (.abs (.group (.binary .add (f "S") (f "S2")))), some "MVK_NO_NUMBER"),
    ("R09", (.binary .subtract (.group (.abs (f "S"))) (.group (.binary .add (f "N") (f "B")))), some "MVK_NO_NUMBER"),
    ("R10", (.binary .add (.group (.binary .subtract (f "N") (f "B"))) (.group (.binary .add (f "N") (f "S")))), some "MVK_NO_NUMBER_FOR_CALC"),
    ("R11", (.binary .add (f "N") (.group (.binary .add (f "S") (f "S2")))), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("R12", (.group (f "S")), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("R13", (.group (.binary .add (f "S") (f "S2"))), some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
    ("U01", (.binary .subtract (.group (.binary .add (f "N") (f "S"))) (f "Nope")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("U02", (.binary .subtract (f "S") (f "Nope")), some "MVK_INVALID_ENTITY"),
    ("U03", (.binary .subtract (f "Nope") (f "S")), some "MVK_INVALID_ENTITY"),
    ("U04", (.binary .add (.abs (f "S")) (f "Nope")), some "MVK_NO_NUMBER"),
    ("U05", (.extremumCall .maximum (.extremum .maximum (f "D") (f "D"))), some "MVK_INVALID_COMPARE_TO_DATE"),
    ("U06", (.extremumCall .maximum (.extremum .maximum (f "D") (f "TM"))), some "MVK_DATEFORMATS_NOT_COMPATIBLE"),
    ("U07", (.extremumCall .maximum (.extremum .maximum (f "TM") (f "D"))), some "MVK_DATEFORMATS_NOT_COMPATIBLE"),
    ("U08", (.binary .add (.extremumCall .maximum (.extremum .maximum (f "N") (f "N2"))) (f "S")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("U09", (.binary .add (f "S") (.extremumCall .maximum (.extremum .maximum (f "N") (f "D")))), some "MVK_NOT_SORTABLE"),
    ("U11", (.power (f "N") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("U12", (.power (f "S") (lit 2)), some "MVK_NO_NUMBER_FOR_CALC"),
    ("U13", (.extremumCall .minimum (.extremum .minimum (f "B") (f "N"))), some "MVK_NOT_SORTABLE"),
    ("U14", (.extremumCall .maximum (.extremum .maximum (f "E") (f "N"))), some "MVK_NOT_SORTABLE"),
    ("V01", (.binary .add (f "T") (f "S")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("V02", (.binary .add (f "S") (f "T")), some "MVK_NO_STRING_OR_NUMBER_FOR_ADD"),
    ("V03", (.binary .subtract (.group (.binary .add (f "T") (f "N"))) (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("V04", (.binary .subtract (f "T") (f "S")), some "MVK_NO_NUMBER_FOR_CALC"),
    ("V05", (.binary .add (.abs (f "S")) (f "T")), some "MVK_NO_NUMBER")]

/- Every row reports the Kernel's code; the failing ids are listed, so a mismatch names its row. -/
example : (rows.filter fun (_, expression, expected) => codeOf expression != expected).map (·.1) =
    [] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.OperationTyping
