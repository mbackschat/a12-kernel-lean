# Condition-class projection grid, 2026-10-01: every ElabError arm on the plain rule comparison.
# Generate with scripts/make-probe-ops.sh condition-class.spec ops.json from this directory.
field err /Order/Note2
group root /Order
msg m Check.
cond LNotes FieldFilled(Note2) And [/Order/Note] == "x"
cond LNoten FieldFilled(Note2) And [/Order/Note] == 5
cond LNoted FieldFilled(Note2) And [/Order/Note] == "05.03.2024"
cond LNotet FieldFilled(Note2) And [/Order/Note] == "10:15:00"
cond LNotebt FieldFilled(Note2) And [/Order/Note] == True
cond LNotebf FieldFilled(Note2) And [/Order/Note] == False
cond LQtys FieldFilled(Note2) And [/Order/Qty] == "x"
cond LQtyn FieldFilled(Note2) And [/Order/Qty] == 5
cond LQtyd FieldFilled(Note2) And [/Order/Qty] == "05.03.2024"
cond LQtyt FieldFilled(Note2) And [/Order/Qty] == "10:15:00"
cond LQtybt FieldFilled(Note2) And [/Order/Qty] == True
cond LQtybf FieldFilled(Note2) And [/Order/Qty] == False
cond LAmounts FieldFilled(Note2) And [/Order/Amount] == "x"
cond LAmountn FieldFilled(Note2) And [/Order/Amount] == 5
cond LAmountd FieldFilled(Note2) And [/Order/Amount] == "05.03.2024"
cond LAmountt FieldFilled(Note2) And [/Order/Amount] == "10:15:00"
cond LAmountbt FieldFilled(Note2) And [/Order/Amount] == True
cond LAmountbf FieldFilled(Note2) And [/Order/Amount] == False
cond LDues FieldFilled(Note2) And [/Order/Due] == "x"
cond LDuen FieldFilled(Note2) And [/Order/Due] == 5
cond LDued FieldFilled(Note2) And [/Order/Due] == "05.03.2024"
cond LDuet FieldFilled(Note2) And [/Order/Due] == "10:15:00"
cond LDuebt FieldFilled(Note2) And [/Order/Due] == True
cond LDuebf FieldFilled(Note2) And [/Order/Due] == False
cond LAts FieldFilled(Note2) And [/Order/At] == "x"
cond LAtn FieldFilled(Note2) And [/Order/At] == 5
cond LAtd FieldFilled(Note2) And [/Order/At] == "05.03.2024"
cond LAtt FieldFilled(Note2) And [/Order/At] == "10:15:00"
cond LAtbt FieldFilled(Note2) And [/Order/At] == True
cond LAtbf FieldFilled(Note2) And [/Order/At] == False
cond LStamps FieldFilled(Note2) And [/Order/Stamp] == "x"
cond LStampn FieldFilled(Note2) And [/Order/Stamp] == 5
cond LStampd FieldFilled(Note2) And [/Order/Stamp] == "05.03.2024"
cond LStampt FieldFilled(Note2) And [/Order/Stamp] == "10:15:00"
cond LStampbt FieldFilled(Note2) And [/Order/Stamp] == True
cond LStampbf FieldFilled(Note2) And [/Order/Stamp] == False
cond LWindows FieldFilled(Note2) And [/Order/Window] == "x"
cond LWindown FieldFilled(Note2) And [/Order/Window] == 5
cond LWindowd FieldFilled(Note2) And [/Order/Window] == "05.03.2024"
cond LWindowt FieldFilled(Note2) And [/Order/Window] == "10:15:00"
cond LWindowbt FieldFilled(Note2) And [/Order/Window] == True
cond LWindowbf FieldFilled(Note2) And [/Order/Window] == False
cond LFlags FieldFilled(Note2) And [/Order/Flag] == "x"
cond LFlagn FieldFilled(Note2) And [/Order/Flag] == 5
cond LFlagd FieldFilled(Note2) And [/Order/Flag] == "05.03.2024"
cond LFlagt FieldFilled(Note2) And [/Order/Flag] == "10:15:00"
cond LFlagbt FieldFilled(Note2) And [/Order/Flag] == True
cond LFlagbf FieldFilled(Note2) And [/Order/Flag] == False
cond LSigneds FieldFilled(Note2) And [/Order/Signed] == "x"
cond LSignedn FieldFilled(Note2) And [/Order/Signed] == 5
cond LSignedd FieldFilled(Note2) And [/Order/Signed] == "05.03.2024"
cond LSignedt FieldFilled(Note2) And [/Order/Signed] == "10:15:00"
cond LSignedbt FieldFilled(Note2) And [/Order/Signed] == True
cond LSignedbf FieldFilled(Note2) And [/Order/Signed] == False
cond LPlains FieldFilled(Note2) And [/Order/Plain] == "x"
cond LPlainn FieldFilled(Note2) And [/Order/Plain] == 5
cond LPlaind FieldFilled(Note2) And [/Order/Plain] == "05.03.2024"
cond LPlaint FieldFilled(Note2) And [/Order/Plain] == "10:15:00"
cond LPlainbt FieldFilled(Note2) And [/Order/Plain] == True
cond LPlainbf FieldFilled(Note2) And [/Order/Plain] == False
cond LLabelleds FieldFilled(Note2) And [/Order/Labelled] == "x"
cond LLabelledn FieldFilled(Note2) And [/Order/Labelled] == 5
cond LLabelledd FieldFilled(Note2) And [/Order/Labelled] == "05.03.2024"
cond LLabelledt FieldFilled(Note2) And [/Order/Labelled] == "10:15:00"
cond LLabelledbt FieldFilled(Note2) And [/Order/Labelled] == True
cond LLabelledbf FieldFilled(Note2) And [/Order/Labelled] == False
cond O01 FieldFilled(Note2) And [/Order/Signed] == False
cond O02 FieldFilled(Note2) And [/Order/Due] == [/Order/At]
cond O03 FieldFilled(Note2) And [/Order/Due] == [/Order/Stamp]
cond O04 FieldFilled(Note2) And [/Order/At] == Today
cond O05 FieldFilled(Note2) And [/Order/Due] == Now
cond O06 FieldFilled(Note2) And [/Order/Due] == BaseYear
cond O07 FieldFilled(Note2) And [/Order/Qty] == BaseYear
cond O08 FieldFilled(Note2) And Length([/Order/Qty]) > 2
cond O09 FieldFilled(Note2) And Length([/Order/Note]) > 2
cond O10 FieldFilled(Note2) And [/Order/Note] == [/Order/Qty]
cond O11 FieldFilled(Note2) And [/Order/Plain] == [/Order/Wide]
cond O12 FieldFilled(Note2) And [/Order/Plain] == [/Order/Swapped]
cond O13 FieldFilled(Note2) And [/Order/Plain] == "PENDING"
cond O14 FieldFilled(Note2) And [/Order/Due] == Today
cond O15 FieldFilled(Note2) And [/Order/Stamp] == Now
cond O16 FieldFilled(Note2) And [/Order/Note] == [/Order/Note]
row LNotes err LNotes m root
row LNoten err LNoten m root
row LNoted err LNoted m root
row LNotet err LNotet m root
row LNotebt err LNotebt m root
row LNotebf err LNotebf m root
row LQtys err LQtys m root
row LQtyn err LQtyn m root
row LQtyd err LQtyd m root
row LQtyt err LQtyt m root
row LQtybt err LQtybt m root
row LQtybf err LQtybf m root
row LAmounts err LAmounts m root
row LAmountn err LAmountn m root
row LAmountd err LAmountd m root
row LAmountt err LAmountt m root
row LAmountbt err LAmountbt m root
row LAmountbf err LAmountbf m root
row LDues err LDues m root
row LDuen err LDuen m root
row LDued err LDued m root
row LDuet err LDuet m root
row LDuebt err LDuebt m root
row LDuebf err LDuebf m root
row LAts err LAts m root
row LAtn err LAtn m root
row LAtd err LAtd m root
row LAtt err LAtt m root
row LAtbt err LAtbt m root
row LAtbf err LAtbf m root
row LStamps err LStamps m root
row LStampn err LStampn m root
row LStampd err LStampd m root
row LStampt err LStampt m root
row LStampbt err LStampbt m root
row LStampbf err LStampbf m root
row LWindows err LWindows m root
row LWindown err LWindown m root
row LWindowd err LWindowd m root
row LWindowt err LWindowt m root
row LWindowbt err LWindowbt m root
row LWindowbf err LWindowbf m root
row LFlags err LFlags m root
row LFlagn err LFlagn m root
row LFlagd err LFlagd m root
row LFlagt err LFlagt m root
row LFlagbt err LFlagbt m root
row LFlagbf err LFlagbf m root
row LSigneds err LSigneds m root
row LSignedn err LSignedn m root
row LSignedd err LSignedd m root
row LSignedt err LSignedt m root
row LSignedbt err LSignedbt m root
row LSignedbf err LSignedbf m root
row LPlains err LPlains m root
row LPlainn err LPlainn m root
row LPlaind err LPlaind m root
row LPlaint err LPlaint m root
row LPlainbt err LPlainbt m root
row LPlainbf err LPlainbf m root
row LLabelleds err LLabelleds m root
row LLabelledn err LLabelledn m root
row LLabelledd err LLabelledd m root
row LLabelledt err LLabelledt m root
row LLabelledbt err LLabelledbt m root
row LLabelledbf err LLabelledbf m root
row O01 err O01 m root
row O02 err O02 m root
row O03 err O03 m root
row O04 err O04 m root
row O05 err O05 m root
row O06 err O06 m root
row O07 err O07 m root
row O08 err O08 m root
row O09 err O09 m root
row O10 err O10 m root
row O11 err O11 m root
row O12 err O12 m root
row O13 err O13 m root
row O14 err O14 m root
row O15 err O15 m root
row O16 err O16 m root
