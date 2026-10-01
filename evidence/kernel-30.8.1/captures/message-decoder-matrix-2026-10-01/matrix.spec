# Message decoder acceptance matrix, 2026-10-01: spacing, category name ends, keyed group position, literals containing For, RuleGroup, per-parameter checks.
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mW01 Check $Grade->Band$.
msg mW02 Check $Grade -> Band$.
msg mW03 Check $Grade-> Band$.
msg mW04 Check $Grade->Band $.
msg mW05 Check $Grade ->Band$.
msg mW06 Check $ Grade->Band$.
msg mW07 Check $Grade-> $.
msg mW08 Check $Grade->$.
msg mW09 Check $Score-> $.
msg mW10 Check $Grade->Band x$.
msg mW11 Check $Grade->Band.value$.
msg mW12 Check $Grade->Band/Foo$.
msg mW13 Check $Grade->Nope x$.
msg mW14 Check $Score->Band x$.
msg mW15 Check $ Score$.
msg mW16 Check $Score $.
msg mW17 Check $Score .value$.
msg mW18 Check $Score. value$.
msg mW20 Check $Score For  "k"$.
msg mW21 Check $Score For"k"$.
msg mW22 Check $Score  For "k"$.
msg mG01 Check $#Cases For "k"$.
msg mG02 Check $#Cases For Score$.
msg mG03 Check $#Cases For Score For "k"$.
msg mG04 Check $#Cases For Nope$.
msg mG05 Check $#Cases$.
msg mL01 Check $Score For "a For b"$.
msg mL02 Check $Score For Grade For "a For b"$.
msg mR01 Check $RuleGroup For Score For "k"$.
msg mR02 Check $Score For RuleGroup$.
msg mP01 Check $Nope$ and $Score$.
msg mP02 Check $Nope$ and $Gradé$.
msg mP03 Check $Nope$ and $Nope2$.
msg mS01 Check $Nope For Score.x$.
msg mS02 Check $Nope For "k" x$.
msg mC01 Check $Score$.
row W01 err c mW01 cases
row W02 err c mW02 cases
row W03 err c mW03 cases
row W04 err c mW04 cases
row W05 err c mW05 cases
row W06 err c mW06 cases
row W07 err c mW07 cases
row W08 err c mW08 cases
row W09 err c mW09 cases
row W10 err c mW10 cases
row W11 err c mW11 cases
row W12 err c mW12 cases
row W13 err c mW13 cases
row W14 err c mW14 cases
row W15 err c mW15 cases
row W16 err c mW16 cases
row W17 err c mW17 cases
row W18 err c mW18 cases
row W20 err c mW20 cases
row W21 err c mW21 cases
row W22 err c mW22 cases
row G01 err c mG01 cases
row G02 err c mG02 cases
row G03 err c mG03 cases
row G04 err c mG04 cases
row G05 err c mG05 cases
row L01 err c mL01 cases
row L02 err c mL02 cases
row R01 err c mR01 cases
row R02 err c mR02 cases
row P01 err c mP01 cases
row P02 err c mP02 cases
row P03 err c mP03 cases
row S01 err c mS01 cases
row S02 err c mS02 cases
row C01 err c mC01 cases
