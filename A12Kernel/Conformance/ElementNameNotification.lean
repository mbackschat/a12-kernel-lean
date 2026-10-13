import A12Kernel.Elaboration.ElementNameNotification

/-! # Locks on the notifications element names, group declarations and element texts raise

Each group mirrors rows of the retained capture
`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/` and cites them by id. The
assertion is the sorted capture labels, because the Kernel reports a set whose order carries no claim.
The whole-model aggregation, with the path walk and the element annotations, is replayed by the
evidence projection, not here.
-/

namespace A12Kernel.Conformance.ElementNameNotification

open A12Kernel

private def english : StringPatternMessageTokens := { field := "field", fieldValue := "field.value" }

private def messageCodes (carrier : FieldMessageCarrier) (entries : List (String × String))
    (locales : List String := ["en_US"]) : List String :=
  (fieldMessageDiagnostics english locales carrier
    (entries.map fun (locale, text) => { locale, text })).map (·.kernelCode)

/-- The stand-in the model reader writes for a lone surrogate, so a text carries the defect. -/
private def lone : String := String.singleton loneSurrogateStandIn

/- A lone surrogate in a field message is the first text gate: the encoding class stands alone for
   the field, from the first failing declared locale, in place of the character or parameter class the
   same text would otherwise draw, and a locale the model does not declare is never asked (we-s, we-e,
   spec/11 Part A). -/
example :
    messageCodes .stringPattern [("en_US", "bad " ++ lone)] = ["WRONG_ENCODING"] ∧
    messageCodes .enumerationInvalidValue [("en_US", lone)] = ["WRONG_ENCODING"] ∧
    messageCodes .stringPattern [("en_US", "a\t" ++ lone)] = ["WRONG_ENCODING"] ∧
    messageCodes .stringPattern [("en_US", "$bogus$ " ++ lone)] = ["WRONG_ENCODING"] ∧
    messageCodes .stringPattern [("en_US", "a\tb"), ("de_DE", lone)] ["en_US", "de_DE"] =
      ["INVALID_CHARACTERS"] ∧
    messageCodes .stringPattern [("en_US", "ok"), ("de_DE", lone)] ["en_US", "de_DE"] =
      ["WRONG_ENCODING"] ∧
    messageCodes .stringPattern [("fr_FR", lone), ("en_US", "ok")] = [] := by
  native_decide


private def sorted (labels : List String) : List String := labels.mergeSort (· ≤ ·)

private def labelsOf (kinds : List ElementNameKind) : List String := sorted (kinds.map (·.label))

/-- A field name under the English condition language, below the given path. -/
private def field (name : String) (above : PathAbove := {}) : List String :=
  labelsOf ((fieldName "value" name).reported above)

private def nested (name : String) (above : PathAbove := {}) : List String :=
  labelsOf ((groupName false name).reported above)

private def root (name : String) : List String :=
  labelsOf ((groupName true name).reported {})

private def sixtyOne (letter : Char) : String := String.ofList (List.replicate 61 letter)

/- A field name's alphabet is `[A-Za-z0-9_:.]`: any other character, a dot before a non-letter or at
   the end, is refused with the path class and the field's own codeless shape, and a leading digit adds
   the path class beside its own name class (pa-f-dash, pa-f-uml, dc-path, dg-f, dg-twin, dg-mixed,
   dc-1, dc-colon, us-field, ps-f61). -/
example :
    field "Co-de" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "Slöts" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "Co.1de" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "Co._de" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "Co..de" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "Co." = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "1Code" = ["MVK_NAME_STARTS_WITH_DIGIT_A12_DV", "MVK_PATH_INVALID"] ∧
    field "1Co.de" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV", "MVK_NAME_STARTS_WITH_DIGIT_A12_DV",
      "MVK_PATH_INVALID"] ∧
    field "Code1" = [] ∧ field "_Slots" = [] ∧ field (sixtyOne 'F') = [] ∧
    field "Co.de" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    field ":Code" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV"] := by
  native_decide

/- A refused character withholds the carrier's name classes, and a slash is its own class unless the
   name is refused otherwise, when it counts as a refused character (pa-slash, pa-slash-bad, spec/11
   `1Codeé`, `xmlCodeé`). -/
example :
    field "Co/de" = ["MVK_PATHS_INCONSISTENT"] ∧
    field "Co/-de" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "1Codeé" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] ∧
    field "xmlCodeé" = ["MVK_PATH_INVALID", "codeless:field-name-shape"] := by
  native_decide

/- A field name beginning `xml` in any case draws its own class, and a dotted name whose last segment
   is the condition language's value word draws the invalid-name class, in either case and only in
   that language's word (xf-1, xf-mixed, xf-dot, nv-val, nv-bare, nv-values, nv-mid, nv-upper,
   nv-de, nv-de-en, nv-de-lower). -/
example :
    field "xmlCode" = ["MVK_NAME_STARTS_WITH_XML_A12_DV"] ∧
    field "xMlCode" = ["MVK_NAME_STARTS_WITH_XML_A12_DV"] ∧
    field "xml.a" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV", "MVK_NAME_STARTS_WITH_XML_A12_DV"] ∧
    field "Code.value" = ["MVK_NAME_INVALID_A12_DV", "MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    field "value" = [] ∧
    field "Code.values" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    field "Code.value.List" = ["MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    field "Code.VALUE" = ["MVK_NAME_INVALID_A12_DV", "MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    labelsOf ((fieldName "Wert" "Code.Wert").reported {}) =
      ["MVK_NAME_INVALID_A12_DV", "MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    labelsOf ((fieldName "Wert" "Code.value").reported {}) = ["MVK_NAME_INVALID_DOT_COLON_A12_DV"] ∧
    labelsOf ((fieldName "Wert" "Code.wert").reported {}) =
      ["MVK_NAME_INVALID_A12_DV", "MVK_NAME_INVALID_DOT_COLON_A12_DV"] := by
  native_decide

/- A supplementary scalar in a field name is the repertoire notification in place of the name's own
   codeless shape (ux-fname). -/
example : field "Code😀" = ["MVK_PATH_INVALID", "codeless:supplementary-character"] := by
  native_decide

/- Whether a name carries a path class of its own is a separate fact from whether it is reported:
   a field named like its parent's refused group keeps its own shape, its name classes and the codeless
   notification its ancestor hands down, but not a second path class (pa-g-and-f, pa-desc-content). -/
example :
    let below : PathAbove := { pathClass := true, codeless := [.groupNameShape] }
    field "Co-de" below = ["codeless:field-name-shape", "codeless:group-name-shape"] ∧
    field "1B" below = ["MVK_NAME_STARTS_WITH_DIGIT_A12_DV", "codeless:group-name-shape"] ∧
    (fieldName "value" "Co-de").pathClass = true ∧ (fieldName "value" "Code").pathClass = false ∧
    (fieldName "value" "Co/de").pathClass = true := by
  native_decide

/- A nested group's alphabet is letters, digits, underscore and the German umlauts and `ß`, and it must
   begin with a letter or an underscore: a refusal is the path class plus the group's codeless shape,
   which every element below it also draws; more than sixty characters is the shape alone
   (pa-g-uml, pa-g-lead, pa-g-dot, dg-nested, ps-60, ps-61). -/
example :
    nested "Teilä" = [] ∧
    nested "äTeil" = ["MVK_PATH_INVALID", "codeless:group-name-shape"] ∧
    nested "Gr-p" = ["MVK_PATH_INVALID", "codeless:group-name-shape"] ∧
    nested "Gr.p" = ["MVK_PATH_INVALID", "codeless:group-name-shape"] ∧
    nested "1Grp" = ["MVK_PATH_INVALID", "codeless:group-name-shape"] ∧
    nested (sixtyOne 'G') = ["codeless:group-name-shape"] ∧
    nested (String.ofList (List.replicate 60 'G')) = [] ∧
    (groupName false "Gr-p").descendantCodeless = [.groupNameShape] ∧
    (groupName false (sixtyOne 'G')).descendantCodeless = [.groupNameShape] ∧
    (groupName false (sixtyOne 'G')).pathClass = false ∧
    (groupName false "Gr-p").pathClass = true := by
  native_decide

/- A nested group reserves a leading underscore for `__meta` exactly and names beginning
   `__attachment_meta` (us-1, us-meta, us-photo, us-meta-x, us-att-data). -/
example :
    nested "_Grp" = ["NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN"] ∧
    nested "__meta" = [] ∧ nested "__attachment_meta_photo" = [] ∧
    nested "__meta_x" = ["NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN"] ∧
    nested "__attachment_metadata" = [] := by
  native_decide

/- A group beginning `xml` in any case draws its own class, an ancestor beginning `xml` hands it to
   every group below, and a path class on the group or on an ancestor withholds it (xg-1, xg-twin,
   xg-mixed, xg-chain, xg-refused, pa-g-and-xml). -/
example :
    nested "xmlGrp" = ["MVK_NAME_STARTS_WITH_XML"] ∧
    nested "Grpxml" = [] ∧ nested "XmLGrp" = ["MVK_NAME_STARTS_WITH_XML"] ∧
    nested "B" { xml := true } = ["MVK_NAME_STARTS_WITH_XML"] ∧
    nested "xmlGé" = ["MVK_PATH_INVALID", "codeless:group-name-shape"] ∧
    nested "xmlSub" { pathClass := true, codeless := [.groupNameShape] } =
      ["codeless:group-name-shape"] ∧
    ((groupName false "xmlA").below {}).xml = true ∧
    ((groupName false "Gr-p").below {}) = { pathClass := true, codeless := [.groupNameShape] } := by
  native_decide

/- A supplementary scalar in a group name replaces the group's codeless shape, and the one handed
   below, with the repertoire notification, which a rule below also draws (ux-gname). -/
example :
    nested "Gr😀" = ["MVK_PATH_INVALID", "codeless:supplementary-character"] ∧
    (groupName false "Gr😀").descendantCodeless = [.supplementaryCharacter] ∧
    ((groupName false "Gr😀").below {}).codeless = [.supplementaryCharacter] ∧
    (((groupName false "Gr😀").below {}).forRule = [.supplementaryCharacter]) ∧
    (((groupName false "Gr-p").below {}).forRule = []) := by
  native_decide

/- A root group's alphabet is the same without the leading restriction: a refusal is the path class,
   the root's own shape and a group shape below; a leading digit is its own class with no path class;
   a leading underscore and a leading umlaut are admitted; and exactly `Id` in any case is reserved,
   whole-name only (pa-root-dash, root-61, dg-root, xr-root, us-root, root-us-meta, root-uml-lead,
   rid-1, rid-mixed, rid-twin). -/
example :
    root "Ro-ot" = ["MVK_PATH_INVALID", "codeless:root-name-shape"] ∧
    (groupName true "Ro-ot").descendantCodeless = [.groupNameShape] ∧
    root (sixtyOne 'R') = ["codeless:name-above-sixty"] ∧
    (groupName true (sixtyOne 'R')).descendantCodeless = [.groupNameShape] ∧
    root "1Root" = ["MVK_NAME_STARTS_WITH_DIGIT"] ∧
    root "xmlRoot" = ["MVK_NAME_STARTS_WITH_XML"] ∧
    root "_Orders" = [] ∧ root "__metaX" = [] ∧ root "äRoot" = [] ∧
    root "Id" = ["MVK_ROOT_GROUP_NAME_INVALID"] ∧ root "iD" = ["MVK_ROOT_GROUP_NAME_INVALID"] ∧
    root "ID" = ["MVK_ROOT_GROUP_NAME_INVALID"] ∧ root "BinId" = [] ∧ root "Identity" = [] := by
  native_decide

/- A group's repeatability has its carrier's ceiling, a root group at 999999999 and a nested group at
   1999999999, and a group with sort fields must be repeatable, a root group included (mt-n, mt-n-twin,
   mt-r, mt-r-twin, si-1, si-empty, si-rep, si-root). -/
example :
    groupDeclarationKinds true (some 1000000000) 0 = [.maxTooBig] ∧
    groupDeclarationKinds true (some 999999999) 0 = [] ∧
    groupDeclarationKinds false (some 2000000000) 0 = [.maxTooBig] ∧
    groupDeclarationKinds false (some 1999999999) 0 = [] ∧
    groupDeclarationKinds false (some 1) 1 = [.invalidSortInfo] ∧
    groupDeclarationKinds false none 1 = [.invalidSortInfo] ∧
    groupDeclarationKinds true none 1 = [.invalidSortInfo] ∧
    groupDeclarationKinds false (some 3) 1 = [] ∧
    groupDeclarationKinds false (some 1) 0 = [] := by
  native_decide

/- A rule and a computation share the rule-name alphabet, and a computation's name is also judged by
   the error-code content law: a hyphen draws both classes and an umlaut or a leading digit the name
   class alone, while a rule name is never judged by the code law (rn-digit, rn-dash, rn-umlaut,
   rn-xml, cpn-digit, cpn-dash, cpn-umlaut). -/
example :
    let labels (kind : ExecutableDeclarationKind) (name : String) : List String :=
      sorted (({ group := ["Form"], name, kind } : ExecutableDeclaration).notifications.filterMap
        (·.kind.label?))
    let rule : ExecutableDeclarationKind := .rule (.text "C")
    labels rule "1R" = ["codeless:rule-name-content"] ∧
    labels rule "R-x" = ["codeless:rule-name-content"] ∧
    labels rule "Rä" = ["codeless:rule-name-content"] ∧
    labels rule "xmlR" = [] ∧ labels rule "Rx" = [] ∧
    labels .computation "1C" = ["codeless:rule-name-content"] ∧
    labels .computation "C-x" = ["codeless:code-content", "codeless:rule-name-content"] ∧
    labels .computation "Cä" = ["codeless:rule-name-content"] ∧
    labels .computation "Cx" = [] := by
  native_decide


private def javaCompiler : StringPatternCompiler :=
  fun source => if source == "(" then none else some fun _ => true

/-- The sorted labels one field raises, with its messages reached or withheld. -/
private def fieldLabels (declaration : FieldTypeDeclaration) (reached : Bool := true)
    (locales : List String := ["en_US"]) : List String :=
  match declaration.judge javaCompiler
      { declaredLocales := locales, messageTokens := english, messagesReached := reached } with
  | .modelNotBuilt => [modelNotBuiltLabel]
  | .notifications raised => sorted (raised.map (·.label))

private def message (locale text : String) : FieldMessageEntry := { locale, text }

/- A String pattern message and an Enumeration invalid-value message are repertoire carriers: a
   supplementary scalar of a declared locale's text is one codeless notification on the field, beside
   the encoding class for a lone surrogate and alone for an ordinary supplementary scalar; a locale
   the model does not declare is not asked (we-s, we-e, spec/01 §1.1). -/
example :
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" ("bad " ++ lone)] }) =
      ["WRONG_ENCODING", "codeless:supplementary-character"] ∧
    fieldLabels (.enumeration { values := [{ token := "A" }], messages := [message "en_US" lone] }) =
      ["WRONG_ENCODING", "codeless:supplementary-character"] ∧
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" "bad 😀"] }) =
      ["codeless:supplementary-character"] ∧
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" "bad",
      message "fr_FR" "😀"] }) = [] := by
  native_decide

/- A supplementary scalar the invalid-character class names is not a repertoire defect of the message,
   while a control character beside an emoji draws both (we-authored, we-control-emoji); the model reader
   reads an authored `U+10FFFF` as `U+10FFFE`, so the field never meets the encoding class. -/
example :
    let noncharacter := "bad " ++ String.singleton (Char.ofNat 0x10FFFE)
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" noncharacter] }) =
      ["INVALID_CHARACTERS"] ∧
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" "bad \u0007 😀"] }) =
      ["INVALID_CHARACTERS", "codeless:supplementary-character"] := by
  native_decide

/- A field whose own name carries a path class reports no field message: its messages are withheld
   while its body classes stay as the context says (pa-f-content, spec/11). -/
example :
    fieldLabels (.string { pattern := some "[A-Z]+", messages := [message "en_US" ("bad " ++ lone)] })
      (reached := false) = [] ∧
    fieldLabels (.string { noValueValidation := true, pattern := some "[A-Z]+", messages :=
      [message "en_US" "bad 😀"] }) (reached := false) =
      ["MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK", "MVK_STRING_TYPE_PARAMS_INCONSISTENT"] := by
  native_decide

/- A slash in a group name, root or nested, is the path-consistency class alone and carries a path class
   below it; no capture row measures it, so this locks the choice that a group follows the field law,
   and equally that an `xml` root hands its prefix to the groups below it. -/
example :
    nested "Gr/p" = ["MVK_PATHS_INCONSISTENT"] ∧ root "Ro/ot" = ["MVK_PATHS_INCONSISTENT"] ∧
    ((groupName false "Gr/p").below {}).pathClass = true ∧
    ((groupName false "Gr/p").below {}).codeless = [] ∧
    nested "Sub" ((groupName true "xmlRoot").below {}) = ["MVK_NAME_STARTS_WITH_XML"] := by
  native_decide

end A12Kernel.Conformance.ElementNameNotification
