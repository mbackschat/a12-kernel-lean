/-! # The condition and operation language: tokens, keywords and parse trees

The DSL a DM model writes its rule conditions, computation operations and preconditions in, as
[`spec/12-concrete-syntax.md`](../../../spec/12-concrete-syntax.md) describes it. This module owns the
lexical layer and the parse tree; `Parser.lean` owns the grammar and the lowering modules own meaning.

The parse tree is deliberately untyped: one `Expr` holds conditions and operations alike, and a call
keeps its arguments as written. Which argument shapes an operator admits is the lowering's question,
so the tree retains every distinction a later static-legality pass needs, the parenthesised argument
and the braced condition included, instead of refusing them here with a guessed class.

Keyword spellings are the a12-dmkits operator catalog's English and German pairs plus the five forms
it does not list (`In`, the range keyword, `RuleGroup`, `@SuppressWarning`, `ValueNotConsistent`),
each mapped to its English spelling as the language-neutral id. A model's language selects one table,
with no fallback to the other (spec §12.1).
-/

namespace A12Kernel.Dm

/-- The keyword pairs, English first. Spellings are case-exact; the case families spec §12.1 admits
are added by `keywordId?`. -/
def keywordPairs : List (String × String) := [
  ("FieldFilled", "FeldAngegeben"), ("FieldNotFilled", "FeldNichtAngegeben"),
  ("And", "Und"), ("Or", "Oder"),
  ("DiffersWithToleranceRange1", "UngleichMitToleranz1"),
  ("DiffersWithToleranceRange2", "UngleichMitToleranz2"),
  ("DiffersWithToleranceRange5", "UngleichMitToleranz5"),
  ("DiffersWithToleranceRange10", "UngleichMitToleranz10"),
  ("AllFieldsFilled", "AlleFelderAngegeben"), ("NoFieldFilled", "KeinFeldAngegeben"),
  ("AtLeastOneFieldFilled", "MindestensEinFeldAngegeben"),
  ("NotAllFieldsFilled", "NichtAlleFelderOderKeinFeldAngegeben"),
  ("FieldsNotCollectivelyFilled", "FelderNichtGemeinsamAngegeben"),
  ("NotExactlyOneFieldFilled", "NichtGenauEinFeldAngegeben"),
  ("MoreThanOneFieldFilled", "MehrAlsEinFeldAngegeben"),
  ("GroupFilled", "KontextAngegeben"), ("GroupNotFilled", "KontextNichtAngegeben"),
  ("AllGroupsFilled", "AlleKontexteAngegeben"), ("NoGroupFilled", "KeinKontextAngegeben"),
  ("AtLeastOneGroupFilled", "MindestensEinKontextAngegeben"),
  ("NotAllGroupsFilled", "NichtAlleOderKeinKontextAngegeben"),
  ("GroupsNotCollectivelyFilled", "KontexteNichtGemeinsamAngegeben"),
  ("True", "Wahr"), ("False", "Falsch"), ("Length", "Laenge"),
  ("PatternMatched", "WieMuster"), ("PatternViolated", "NichtWieMuster"),
  ("FieldValueIncludedInValueList", "FeldWertInWerteListe"),
  ("FieldValueNotIncludedInValueList", "FeldWertNichtInWerteListe"),
  ("AtLeastOneFieldValueIncludedInValueList", "MindestensEinFeldWertInWerteListe"),
  ("NoFieldValueIncludedInValueList", "KeinFeldWertInWerteListe"),
  ("NotAllFieldValuesIncludedInValueList", "NichtAlleFeldWerteInWerteListe"),
  ("NumberOfFilledFields", "AnzahlAngegebenerFelder"),
  ("NumberOfFilledGroups", "AnzahlAngegebenerKontexte"),
  ("RepetitionNotUnique", "WiederholungNichtEindeutig"), ("@From", "@Von"),
  ("FieldValuesNotUnique", "FeldWerteNichtEindeutig"),
  ("Sum", "Summe"), ("MaxValue", "MaxWert"), ("MinValue", "MinWert"),
  ("RoundDown", "Abrunden"), ("RoundDownValue", "AbrundenWert"), ("RoundUpValue", "AufrundenWert"),
  ("RoundAccountingValue", "RundenWert"), ("AbsValue", "AbsWert"), ("Abs", "Abs"),
  ("Min", "Min"), ("Max", "Max"), ("RoundUp", "Aufrunden"), ("RoundAccounting", "Runden"),
  ("NumberOfDifferentValues", "AnzahlVerschiedenerWerte"),
  ("NumberOfValueInFields", "AnzahlWertInFeldliste"),
  ("Having", "Mit"), ("CurrentRepetition", "AktuelleWiederholung"),
  ("CustomCondition", "ApplikationsBedingung"), ("For", "Fuer"),
  ("Today", "Heute"),
  ("DifferenceInDays", "DifferenzInTagen"), ("DifferenceInMonths", "DifferenzInMonaten"),
  ("DifferenceInYears", "DifferenzInJahren"), ("DifferenceInHours", "DifferenzInStunden"),
  ("DifferenceInMinutes", "DifferenzInMinuten"), ("DifferenceInSeconds", "DifferenzInSekunden"),
  ("AddDays", "AddiereTage"), ("AddMonths", "AddiereMonate"), ("AddYears", "AddiereJahre"),
  ("AddHours", "AddiereStunden"), ("AddMinutes", "AddiereMinuten"), ("AddSeconds", "AddiereSekunden"),
  ("YearFromDate", "JahrAusDatum"), ("MonthFromDate", "MonatAusDatum"), ("DayFromDate", "TagAusDatum"),
  ("QuarterFromDate", "QuartalAusDatum"),
  ("StartOfDateRange", "StartAusDatumBereich"), ("EndOfDateRange", "EndeAusDatumBereich"),
  ("DateRangesOverlap", "DatumsBereicheUeberlappend"),
  ("AtLeastOneDateRangeOverlaps", "MindestensEinDatumsBereichUeberlappend"),
  ("HoursFromTime", "StundenAusZeit"), ("MinutesFromTime", "MinutenAusZeit"),
  ("SecondsFromTime", "SekundenAusZeit"),
  ("DateFromDateTime", "DatumAusDateTime"), ("TimeFromDateTime", "ZeitAusDateTime"),
  ("RangeAsString", "BereichAlsString"), ("FieldValueAsString", "FeldWertAlsString"),
  ("RangeAsNumber", "BereichAlsZahl"), ("FieldValueAsNumber", "FeldWertAlsZahl"),
  ("ValueAsDate", "WertAlsDatum"), ("FirstDay", "ErsterTag"), ("LastDay", "LetzterTag"),
  ("Date", "Datum"), ("Time", "Zeit"), ("DateTime", "DateTime"), ("Now", "Jetzt"),
  ("BaseYear", "Referenzjahr"), ("Valid", "Gueltig"), ("Invalid", "Ungueltig"),
  ("SumOfProducts", "SummeVonProdukten"), ("FirstFilledValue", "ErsterAngegebenerWert"),
  ("DateRange", "DatumBereich"),
  ("RuleGroup", "RegelKontext"), ("@SuppressWarning", "@UnterdrueckeWarnung"),
  ("ValueNotConsistent", "WertNichtKonsistent"), ("To", "Zu")]

inductive Language | english | german
  deriving Repr, BEq, DecidableEq

/-- The language a model's `conditionLanguage` code selects; any other code is refused. -/
def Language.ofCode? : String → Option Language
  | "en_US" => some .english
  | "de_DE" => some .german
  | _ => none

/-- The calls the grammar reads as whole conditions, never as an operation: the field-list, group-list,
value-list, consistency, validity and repetition conditions (`einfacheBedingung`). Written in an
operation's position, one is a token defect at its own position (spec/12 §12.3). -/
def conditionCallIds : List String := [
  "FieldFilled", "FieldNotFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled", "NoFieldFilled",
  "AllFieldsFilled", "FieldsNotCollectivelyFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled",
  "DateRangesOverlap", "FieldValuesNotUnique",
  "GroupFilled", "GroupNotFilled", "AtLeastOneGroupFilled", "NoGroupFilled", "AllGroupsFilled",
  "GroupsNotCollectivelyFilled", "NotAllGroupsFilled",
  "FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList",
  "AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList",
  "NotAllFieldValuesIncludedInValueList", "AtLeastOneDateRangeOverlaps", "ValueNotConsistent",
  "Valid", "Invalid", "RepetitionNotUnique"]

/-- The H-model form constructs, keywords only in a German model and with no English spelling
(spec §12.1: 125 German spellings against 112 English ones). Each is its own id; no lowering admits
one, so a rule naming one is refused by it rather than read as a field. -/
def germanOnlyKeywords : List String := [
  "AktuelleVordruckNummer", "AnzahlAngegebenerVordrucke", "AnzahlAngegebeneUsb", "KeinVordruckAngegeben",
  "MaximalAngegebenerZeilenindex", "MindestensEinVordruckAngegeben", "UsbNichtFortlaufend",
  "VordruckAngegeben", "VordruckNichtAngegeben", "VordruckNichtFortlaufend", "ZeileNichtEindeutig",
  "ZeilenLueckenlos", "ZeilenNichtAufsteigend"]

/-- The keyword a spelling denotes in one language, by its English id. Only the connectives, `In`
and the range keyword admit case variants, each family enumerated rather than case-folded (spec §12.1). -/
def keywordId? (language : Language) (spelling : String) : Option String :=
  let families : List (String × List String) := match language with
    | .english => [("And", ["and", "AND"]), ("Or", ["or", "OR"]), ("To", ["to", "TO"])]
    | .german => [("And", ["und", "UND"]), ("Or", ["oder", "ODER"]), ("To", ["zu", "ZU"])]
  if spelling == "In" || spelling == "in" || spelling == "IN" then some "In"
  else match families.find? (·.2.contains spelling) with
    | some (id, _) => some id
    | none => ((keywordPairs.find? fun (english, german) =>
        spelling == match language with | .english => english | .german => german).map (·.1)).orElse
          fun _ => if language == .german && germanOnlyKeywords.contains spelling then some spelling else none

/-- The Kernel's class for a refused text; spec §12.3.1 owns which one a text draws. -/
inductive SyntaxErrorClass
  | lexer
  | unexpectedToken
  | expectedTokenNotFound
  | incompleteInput
  | bracketMissing
  /-- A segment's `.*` star, the H-model spelling an A12 model refuses (spec/12 §12.3). -/
  | pointInA12Model
  deriving Repr, BEq, DecidableEq

def SyntaxErrorClass.code : SyntaxErrorClass → String
  | .lexer => "MVK_LEXER_STANDARD_ERROR"
  | .unexpectedToken => "MVK_UNEXPECTED_TOKEN"
  | .expectedTokenNotFound => "MVK_EXPECTED_TOKEN_NOT_FOUND"
  | .incompleteInput => "MVK_INCOMPLETE_INPUT"
  | .bracketMissing => "MVK_BRACKET_MISSING"
  | .pointInA12Model => "MVK_POINT_IN_A12_MODEL"

structure SyntaxError where
  errorClass : SyntaxErrorClass
  /-- The character offset the error is raised at. -/
  offset : Nat
  deriving Repr, BEq

inductive Token
  | keyword (id : String)
  | name (text : String) (quoted : Bool := false)
  /-- A number literal's digits and point, whitespace inside it removed (spec §12.3). -/
  | number (text : String)
  | string (text : String)
  | symbol (text : String)
  | comment
  /-- `#Zeile`, lexed in either language and refused by the grammar (spec §12.1). -/
  | rowIteration
  deriving Repr, BEq, DecidableEq, Inhabited

structure Lexeme where
  token : Token
  offset : Nat
  deriving Repr, Inhabited

/-- The five whitespace characters; every other space character is a lexer error (spec §12.1). -/
def isDslWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\r' || c == '\t' || c == '\x0c' || c == '\n'

/-- A name character: ASCII letters, digits, underscore, colon and the German letters. The Kernel lexes
`MVK_GEBÜHR` as one name and refuses `MVK_FRAÉ` lexically (spec §12.4). -/
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == ':' || "äöüÄÖÜß".contains c

private def symbols : List String :=
  ["==", "!=", "<=", ">=", "->", "..", ".", "<", ">", "+", "-", "*", "/", "^", "$", "(", ")", "[", "]",
   "{", "}", ","]

private partial def skipWhitespace (chars : Array Char) (index : Nat) : Nat :=
  if h : index < chars.size then
    if isDslWhitespace chars[index] then skipWhitespace chars (index + 1) else index
  else index

private partial def takeWhile (p : Char → Bool) (chars : Array Char) (index : Nat) : Nat :=
  if h : index < chars.size then
    if p chars[index] then takeWhile p chars (index + 1) else index
  else index

private def slice (chars : Array Char) (start stop : Nat) : String :=
  String.ofList (chars.extract start stop).toList

/-- Split a text into lexemes, or the offset of the first character the lexer cannot take. -/
partial def lex (language : Language) (text : String) (recognizeKeywords : Bool := true) : Except SyntaxError (Array Lexeme) :=
  let chars := text.toList.toArray
  let rec go (index : Nat) (out : Array Lexeme) : Except SyntaxError (Array Lexeme) :=
    let index := skipWhitespace chars index
    if h : index < chars.size then
      let c := chars[index]
      let emit (token : Token) (next : Nat) := go next (out.push { token, offset := index })
      let fail : Except SyntaxError (Array Lexeme) := .error { errorClass := .lexer, offset := index }
      let charAt (offset : Nat) : Option Char := chars[offset]?
      if c == ';' && charAt (index + 1) == some ';' then
        emit .comment (takeWhile (fun c => c != '\r' && c != '\n') chars index)
      else if c == '"' || c == '\'' then
        let stop := takeWhile (· != c) chars (index + 1)
        if stop < chars.size then
          let body := slice chars (index + 1) stop
          emit (if c == '"' then .string body else .name body true) (stop + 1)
        else fail
      else if c.isDigit then
        let integer := takeWhile Char.isDigit chars index
        -- Whitespace may stand on either side of the point (spec §12.3), so look past it before
        -- deciding that the literal has a fractional part.
        let nameEnd := takeWhile isNameChar chars index
        let point := skipWhitespace chars integer
        let fractionStart := skipWhitespace chars (point + 1)
        if nameEnd > integer then
          emit (.name (slice chars index nameEnd)) nameEnd
        else if charAt point == some '.' && (charAt fractionStart).any Char.isDigit then
          let stop := takeWhile Char.isDigit chars fractionStart
          emit (.number (slice chars index integer ++ "." ++ slice chars fractionStart stop)) stop
        else emit (.number (slice chars index integer)) integer
      else if isNameChar c then
        let stop := takeWhile isNameChar chars index
        let word := slice chars index stop
        emit (if recognizeKeywords then
          match keywordId? language word with | some id => .keyword id | none => .name word
          else .name word) stop
      else if c == '@' then
        let stop := takeWhile isNameChar chars (index + 1)
        match keywordId? language (slice chars index stop) with
        | some id => emit (.keyword id) stop
        | none => fail
      else if c == '#' then
        if slice chars index (index + 6) == "#Zeile" then emit .rowIteration (index + 6) else fail
      else
        match symbols.find? fun symbol => slice chars index (index + symbol.length) == symbol with
        | some symbol => emit (.symbol symbol) (index + symbol.length)
        | none => fail
    else .ok out
  go 0 #[]

/-- One path segment, its repetition star kept per segment (spec §10). -/
structure Segment where
  name : String
  star : Bool
  deriving Repr, BEq, DecidableEq

/-- An entity path as written. `correlated` is the `$` form that reads the enclosing filter's row, and
`turningPoint` the `..Name` label naming the ancestor an up-run reaches. Only an up-run may leave
`segments` empty, the reference then being that ancestor group. -/
structure Path where
  correlated : Bool := false
  absolute : Bool := false
  ups : Nat := 0
  turningPoint : Option String := none
  segments : List Segment
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CompareOp
  | eq | ne | lt | le | gt | ge
  | patternMatched | patternViolated
  /-- `DiffersWithToleranceRange<n>`. -/
  | tolerance (range : Nat)
  deriving Repr, BEq, DecidableEq

inductive ArithOp | add | sub | mul | div | pow
  deriving Repr, BEq, DecidableEq

inductive LogicOp | and | or
  deriving Repr, BEq, DecidableEq

mutual
/-- A semantic index key is a literal or a complete entity reference (spec §7.3). -/
inductive IndexKey
  | literal (text : String)
  | reference (key : Reference)
  deriving Repr, BEq

/-- An entity reference retains its category, recursive semantic index and filter as written.
The grammar puts the category before `For`; an entity key owns the following `Having` (spec §7.3). -/
structure Reference where
  path : Path
  index : Option IndexKey := none
  category : Option String := none
  filter : Option Expr := none
  deriving Repr, BEq, Inhabited

/-- A condition or an operation as written. -/
inductive Expr
  /-- A number literal with its optional sign, as its digits spell it. -/
  | number (text : String)
  /-- A quoted literal; whether it is a date, a clock or a String is the lowering's question. -/
  | string (text : String)
  /-- A bracketed read, `[path]`. -/
  | value (reference : Reference)
  /-- A bare entity, which stands only where an operator's argument is typed as one. -/
  | entity (reference : Reference)
  /-- A keyword written without an argument list, such as `Today` or `True`. -/
  | constant (id : String)
  /-- An operator call. `listed` holds the arguments after an `In`, and `scope` an `@From` group. -/
  | call (id : String) (arguments : List Argument) (listed : Option (List Argument))
      (scope : Option Reference)
  | custom (name : String) (quoted : Bool := false)
  | arith (op : ArithOp) (left right : Expr)
  | braces (body : Expr)
  | compare (op : CompareOp) (left right : Expr)
  /-- Two or more parts joined by one connective. -/
  | logic (op : LogicOp) (parts : List Expr)
  | parens (body : Expr)
  deriving Repr, BEq, Inhabited

/-- One call argument, with an optional range end (`To`); references own their filters. -/
inductive Argument
  | mk (expr : Expr) (rangeEnd : Option Expr)
  deriving Repr, BEq, Inhabited
end

/-- A whole condition or operation text: the suppressed warning names of its preamble and its body. -/
structure Text where
  suppressed : List String := []
  body : Expr
  deriving Repr, BEq

end A12Kernel.Dm
