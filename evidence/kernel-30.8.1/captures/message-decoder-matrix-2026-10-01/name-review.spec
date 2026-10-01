# Cold-review settling row for the name position's category arrow after an unknown name, 2026-10-01.
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mN30 Check $Nope->Band x$.
msg mN31 Check $Nope->Band$.
row N30 err c mN30 cases
row N31 err c mN31 cases
