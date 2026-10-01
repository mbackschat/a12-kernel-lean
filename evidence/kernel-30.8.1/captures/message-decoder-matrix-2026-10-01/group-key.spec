# Keyed group position, 2026-10-01, an admitted absolute group as the control.
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mH00 Check $#/Probe/Cases$.
msg mH01 Check $#/Probe/Cases For "k"$.
msg mH02 Check $#/Probe/Cases For Score$.
msg mH03 Check $#/Probe/Cases For Score For "k"$.
msg mH04 Check $#/Probe/Cases For Nope$.
msg mH05 Check $#/Probe/Cases For Grade$.
msg mH06 Check $#/Probe For "k"$.
row H00 err c mH00 cases
row H01 err c mH01 cases
row H02 err c mH02 cases
row H03 err c mH03 cases
row H04 err c mH04 cases
row H05 err c mH05 cases
row H06 err c mH06 cases
