# Corrected spellings, read from `dmtool operators`: an expression operand is [Bracketed], the
# comparison operators are infix, and a category access is [Field -> Category].
field anchor /Probe/Anchor
field amount /Probe/Amount
field note   /Probe/Claims/Note
field score  /Probe/Cases/Score
msg plain plain text

cond q_calcstring FieldFilled(Amount) And [Amount] < [Anchor] + 1
cond q_catunknown FieldFilled(Score) And [Grade -> Nope] == "Hi"
cond q_catnonenum FieldFilled(Anchor) And [Anchor -> Band] == "Hi"
cond q_badvalue   FieldFilled(Score) And [Grade] == "ZZZ"
cond q_enumstring FieldFilled(Score) And [Grade] == [Score]
cond q_tolerstr   FieldFilled(Anchor) And [Anchor] DiffersWithToleranceRange5 [Alpha]
cond q_patconst   FieldFilled(Anchor) And "abc" PatternMatched "a.*"
cond q_patok      FieldFilled(Anchor) And [Anchor] PatternMatched "[A-Z]{2}"
cond q_nostar     FieldFilled(Note) And NumberOfFilledFields(/Probe/Claims/Payout Having [/Probe/Claims/ClaimNo] == "a") > 0
cond q_star       FieldFilled(Note) And NumberOfFilledFields(/Probe/Claims*/Payout Having [/Probe/Claims/ClaimNo] == "a") > 0
cond q_groupfilt  FieldFilled(Note) And NumberOfFilledGroups(/Probe/Claims* Having [/Probe/Claims/ClaimNo] == "a") > 0
cond q_todaynum   FieldFilled(Amount) And [Amount] >= Today
cond q_enumenum   FieldFilled(Score) And [Grade] == [Grade2]
cond q_strnum     FieldFilled(Anchor) And [Anchor] < [Amount]
cond q_yesno      FieldFilled(Anchor) And AllFieldsFilled(Anchor) And [Anchor] == True

row Q00 amount q_calcstring plain
row Q01 score  q_catunknown plain
row Q02 anchor q_catnonenum plain
row Q03 score  q_badvalue   plain
row Q04 score  q_enumstring plain
row Q05 anchor q_tolerstr   plain
row Q06 anchor q_patconst   plain
row Q07 anchor q_patok      plain
row Q08 note   q_nostar     plain
row Q09 note   q_star       plain
row Q10 note   q_groupfilt  plain
row Q11 amount q_todaynum   plain
row Q12 score  q_enumenum   plain
row Q13 anchor q_strnum     plain
row Q14 anchor q_yesno      plain
