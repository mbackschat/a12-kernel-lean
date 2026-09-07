# Rows designed from the Kernel's own guards, not from message text. Spellings taken from
# `dmtool operators` first: bare names inside a call, [Brackets] in an expression position.
field anchor /Probe/Anchor
field amount /Probe/Amount
field note   /Probe/Claims/Note
field score  /Probe/Cases/Score
field other  /Probe/Outer/Inner/Other
field flag   /Probe/Flag
field due    /Probe/Due
msg plain plain text

# controls on the new declarations
cond c_flag FieldFilled(Flag)
cond c_due  FieldFilled(Due)

# checkNoCategories — a category inside an entity list that bans one
cond n_catcount FieldFilled(Score) And NumberOfFilledFields(/Probe/Cases*/Grade -> Band) > 0
cond n_catround FieldFilled(Score) And RoundDown([Grade -> Band], 0) < 1

# checkAllEntitiesInRuleGroup — RepetitionNotUnique over a field outside the rule group
cond n_outside FieldFilled(Note) And RepetitionNotUnique(/Probe/Cases/Grade)
# FromScope over a nonrepeatable group
cond n_fromscope FieldFilled(Note) And RepetitionNotUnique(/Probe/Claims/ClaimNo @From /Probe)

# RangeAsNumber / RangeAsString interval must begin above zero
cond n_interval  FieldFilled(Anchor) And RangeAsNumber(Anchor, 0, 3) == 0
cond n_intervalS FieldFilled(Anchor) And RangeAsString(Anchor, 0, 3) == "AB"

# Confirm / Boolean typing
cond y_confirmstr FieldFilled(Flag) And [Flag] == [Anchor]
cond y_confirmok  FieldFilled(Flag) And [Flag] == True
cond y_boolnum    FieldFilled(Amount) And [Amount] == True

# value lists over the wrong kinds
cond v_enumbad  FieldFilled(Score) And FieldValueIncludedInValueList(Grade, "ZZZ")
cond v_catbad   FieldFilled(Score) And [Grade -> Band] == "ZZZ"
cond v_enumenum FieldFilled(Score) And [/Probe/Cases/Grade] == [/Probe/Cases2/Grade]
cond v_confirmlist FieldFilled(Flag) And FieldValueIncludedInValueList(Flag, "x")

# date operations, now that DATE declarations exist
cond d_addnonnum  AllFieldsFilled(Due, Due2) And [Due2] > AddDays(Due, Anchor)
cond d_constonly  FieldFilled(Due) And DifferenceInDays("01.01.2020", "01.01.2021") > 0
cond d_baddate    FieldFilled(Due) And DifferenceInDays(Due, "99.99.9999") > 0
cond d_noyear     FieldFilled(Due) And DifferenceInDays(Due, "31.12") > 0
cond d_lengthdate FieldFilled(Due) And Length(Due) > 2
cond d_yearok     FieldFilled(Due) And YearFromDate(Due) < 2020

# semantic index shapes
cond s_group   FieldFilled(Note) And FieldFilled(Payout For /Probe/Claims)
cond s_cat     FieldFilled(Score) And FieldFilled(Score For /Probe/Cases/Grade -> Band)

# concatenation and string typing
cond t_concatnum FieldFilled(Anchor) And [Anchor] != [Amount] + "-X"
cond t_lengthnum FieldFilled(Anchor) And Length(Amount) > 2

# rule-context wildcard
cond w_rulegroup FieldFilled(Note) And NumberOfFilledGroups(RuleGroup*) > 0

row R00 flag   c_flag plain
row R01 due    c_due  plain
row R10 score  n_catcount plain
row R11 score  n_catround plain
row R12 note   n_outside  plain
row R13 note   n_fromscope plain
row R14 anchor n_interval  plain
row R15 anchor n_intervalS plain
row R20 flag   y_confirmstr plain
row R21 flag   y_confirmok  plain
row R22 amount y_boolnum    plain
row R30 score  v_enumbad  plain
row R31 score  v_catbad   plain
row R32 score  v_enumenum plain
row R33 flag   v_confirmlist plain
row R40 due    d_addnonnum  plain
row R41 due    d_constonly  plain
row R42 due    d_baddate    plain
row R43 due    d_noyear     plain
row R44 due    d_lengthdate plain
row R45 due    d_yearok     plain
row R50 note   s_group plain
row R51 score  s_cat   plain
row R60 anchor t_concatnum plain
row R61 anchor t_lengthnum plain
row R70 note   w_rulegroup plain
