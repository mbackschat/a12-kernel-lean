import A12Kernel.Reference.Dm.Syntax

/-! # Printing a parse tree back to condition text

The inverse of `parseText` on the trees it produces: every grouping the grammar records is a node of
its own (`parens`, `braces`), so printing each node in place, with keywords spelled in the model's
language, reads back to the same tree. A tree another producer builds must keep that discipline: a
`logic` part that is itself a `logic` needs its `parens` node, as the parser would have made it.

Comments are not part of the tree and are not printed.
-/

namespace A12Kernel.Dm

/-- A keyword's spelling in one language, from its English id. A `Non<Operation>` twin's id is
`Non` before its operation's id and is spelled `Non` before that operation's spelling. -/
def keywordSpelling (language : Language) (id : String) : String :=
  let spell (id : String) : Option String := (keywordPairs.find? (·.1 == id)).map fun (english, german) =>
    match language with | .english => english | .german => german
  match spell id, (if id.startsWith "Non" then spell (id.drop 3).toString else none) with
  | some spelling, _ => spelling
  | none, some base => "Non" ++ base
  | none, none => id

/-- A name, quoted when bare spelling would lex as something else: a keyword, a number, or a word
holding a character no name may. -/
def printName (language : Language) (name : String) : String :=
  let bare := !name.isEmpty && name.all isNameChar && !(name.front.isDigit) &&
    (keywordId? language name).isNone
  if bare then name else "'" ++ name ++ "'"

def printPath (language : Language) (path : Path) : String :=
  let segments := "/".intercalate (path.segments.map fun segment =>
    printName language segment.name ++ (if segment.star then "*" else ""))
  let prefix_ :=
    if path.absolute then "/"
    else if path.ups == 0 then ""
    else
      "/".intercalate (List.replicate path.ups "..") ++
        (path.turningPoint.map (printName language)).getD "" ++
        (if path.segments.isEmpty then "" else "/")
  (if path.correlated then "$" else "") ++ prefix_ ++ segments

def printReference (language : Language) (reference : Reference) : String :=
  let index := match reference.index with
    | none => ""
    | some (.literal text) => s!" {keywordSpelling language "For"} \"{text}\""
    | some (.path key) => s!" {keywordSpelling language "For"} {printPath language key}"
  let category := (reference.category.map fun name => s!" -> {printName language name}").getD ""
  printPath language reference.path ++ index ++ category

def CompareOp.spelling (language : Language) : CompareOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .patternMatched => keywordSpelling language "PatternMatched"
  | .patternViolated => keywordSpelling language "PatternViolated"
  | .tolerance range => keywordSpelling language s!"DiffersWithToleranceRange{range}"

def ArithOp.spelling : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .pow => "^"

mutual
def printExpr (language : Language) : Expr → String
  | .number text => text
  | .string text => "\"" ++ text ++ "\""
  | .value reference => "[" ++ printReference language reference ++ "]"
  | .entity reference => printReference language reference
  | .constant id => keywordSpelling language id
  | .call id arguments listed scope =>
      let listed := match listed with
        | some items => s!" {keywordSpelling language "In"} {printArguments language items}"
        | none => ""
      let scope := match scope with
        | some path => s!" {keywordSpelling language "@From"} {printPath language path}"
        | none => ""
      keywordSpelling language id ++ "(" ++ printArguments language arguments ++ listed ++ scope ++ ")"
  | .custom name quoted =>
      keywordSpelling language "CustomCondition" ++ " " ++
        (if quoted || (keywordId? language name).isSome then "'" ++ name ++ "'" else name)
  | .arith op left right => printExpr language left ++ " " ++ op.spelling ++ " " ++ printExpr language right
  | .braces body => "{" ++ printExpr language body ++ "}"
  | .compare op left right =>
      printExpr language left ++ " " ++ op.spelling language ++ " " ++ printExpr language right
  | .logic op parts =>
      let connective := keywordSpelling language (match op with | .and => "And" | .or => "Or")
      s!" {connective} ".intercalate (printParts language parts)
  | .parens body => "(" ++ printExpr language body ++ ")"

def printParts (language : Language) : List Expr → List String
  | [] => []
  | part :: rest => printExpr language part :: printParts language rest

def printArgument (language : Language) : Argument → String
  | .mk expr rangeEnd filter =>
      printExpr language expr ++
        (match rangeEnd with
          | some finish => s!" {keywordSpelling language "To"} {printExpr language finish}"
          | none => "") ++
        (match filter with
          | some body => s!" {keywordSpelling language "Having"} {printExpr language body}"
          | none => "")

def printArguments (language : Language) : List Argument → String
  | [] => ""
  | [argument] => printArgument language argument
  | argument :: rest => printArgument language argument ++ ", " ++ printArguments language rest
end

def printText (language : Language) (text : Text) : String :=
  let preamble := text.suppressed.map fun name =>
    s!"{keywordSpelling language "@SuppressWarning"}({printName language name}) "
  String.join preamble ++ printExpr language text.body

end A12Kernel.Dm
