# Parser static-legality sweep. One condition per row, plain message, so every row pre-flights its own
# condition (throughput rule 5) and the target class is the condition's own refusal.
field anchor /Probe/Anchor
field amount /Probe/Amount
field note   /Probe/Claims/Note
field score  /Probe/Cases/Score
field other  /Probe/Outer/Inner/Other
field claims /Probe/Claims

msg plain plain text

# --- controls (liveness): each error field admits with an ordinary condition
cond c_anchor FieldFilled(Anchor)
cond c_amount FieldFilled(Amount)
cond c_note   FieldFilled(Note)
cond c_score  FieldFilled(Score)
cond c_other  FieldFilled(Other)

# --- constants and arithmetic
cond k_twoconst   FieldFilled(Anchor) And 1 > 2
cond k_calcstring FieldFilled(Anchor) And Anchor + 1 > 0
cond k_addmixed   FieldFilled(Amount) And Amount + Anchor > 0
cond k_badconst   FieldFilled(Amount) And Amount > Today

# --- enumeration and category
cond e_catunknown FieldFilled(Score) And EnumCategory(Grade, "Nope") == "Hi"
cond e_catnonenum FieldFilled(Anchor) And EnumCategory(Anchor, "Band") == "Hi"
cond e_badvalue   FieldFilled(Score) And Grade == "ZZZ"
cond e_enumstring FieldFilled(Score) And Grade == Anchor
cond e_onlyenums  FieldFilled(Score) And EnumCategory(Score, "Band") == "Hi"

# --- arity
cond a_one   FieldFilled(Anchor, Alpha)
cond a_two   FieldFilled(Anchor) And DiffersWithToleranceRange5(Amount)
cond a_toler FieldFilled(Anchor) And DiffersWithToleranceRange5(Anchor, Alpha)

# --- pattern
cond p_constfirst FieldFilled(Anchor) And PatternMatched("abc", "a.*")

# --- groups where fields are expected and the reverse
cond g_fieldasgroup FieldFilled(Anchor) And NumberOfFilledGroups(Anchor) > 0
cond g_notrepeat    FieldFilled(Anchor) And CurrentRepetition(/Probe) > 0
cond g_wildrule     FieldFilled(Anchor) And NumberOfFilledFields(/Probe*/Alpha) > 0

# --- paths and roots
cond r_badroot   FieldFilled(Anchor) And FieldFilled(/Nope/Alpha)
cond r_notgroup  FieldFilled(Anchor) And NumberOfFilledFields(/Probe/Claims) > 0

# --- semantic index family
cond s_nofield    FieldFilled(Note) And FieldFilled(Payout For Claims)
cond s_withstar   FieldFilled(Note) And FieldFilled(Payout For /Probe/Claims*/ClaimNo)
cond s_withcat    FieldFilled(Score) And FieldFilled(Score For Grade)
cond s_indexbad   FieldFilled(Note) And FieldFilled(Payout For "zz")

# --- filter
cond f_nostar   FieldFilled(Note) And NumberOfFilledFields(/Probe/Claims/Payout Having (ClaimNo == "a")) > 0

# --- date construction
cond d_missingyear FieldFilled(Amount) And DifferenceInDays(Today, "31.12") > 0
cond d_baddate     FieldFilled(Amount) And DifferenceInDays(Today, "99.99.9999") > 0
cond d_onlyconst   FieldFilled(Amount) And DifferenceInDays("01.01.2020", "01.01.2021") > 0

# --- rows
row P00 anchor c_anchor plain
row P01 amount c_amount plain
row P02 note   c_note   plain
row P03 score  c_score  plain
row P04 other  c_other  plain
row P10 anchor k_twoconst   plain
row P11 anchor k_calcstring plain
row P12 amount k_addmixed   plain
row P13 amount k_badconst   plain
row P20 score  e_catunknown plain
row P21 anchor e_catnonenum plain
row P22 score  e_badvalue   plain
row P23 score  e_enumstring plain
row P24 score  e_onlyenums  plain
row P30 anchor a_one   plain
row P31 anchor a_two   plain
row P32 anchor a_toler plain
row P33 anchor p_constfirst plain
row P40 anchor g_fieldasgroup plain
row P41 anchor g_notrepeat    plain
row P42 anchor g_wildrule     plain
row P50 anchor r_badroot  plain
row P51 anchor r_notgroup plain
row P60 note  s_nofield  plain
row P61 note  s_withstar plain
row P62 score s_withcat  plain
row P63 note  s_indexbad plain
row P70 note  f_nostar plain
row P80 amount d_missingyear plain
row P81 amount d_baddate     plain
row P82 amount d_onlyconst   plain
