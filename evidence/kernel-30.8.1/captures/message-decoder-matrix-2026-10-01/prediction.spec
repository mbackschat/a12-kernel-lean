# Name-position prediction span, 2026-10-01: does a syntax fault after a complete entity answer before the entity's own check?
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mN01 Check $Nope x$.
msg mN02 Check $Nope/$.
msg mN03 Check $Nope//Score$.
msg mN04 Check $Score x$.
msg mN05 Check $Score/$.
msg mN06 Check $Nope.Vordruckzeile x$.
msg mN07 Check $Nope.value x$.
msg mN08 Check $Nope For$.
msg mN09 Check $Score For$.
msg mN10 Check $Grade->Nope For$.
msg mN12 Check $BaseYear x$.
msg mN13 Check $BaseYear+$.
msg mN15 Check $RuleGroup$.
msg mN16 Check $RuleGroup->Band$.
msg mN17 Check $RuleGroup x$.
row N01 err c mN01 cases
row N02 err c mN02 cases
row N03 err c mN03 cases
row N04 err c mN04 cases
row N05 err c mN05 cases
row N06 err c mN06 cases
row N07 err c mN07 cases
row N08 err c mN08 cases
row N09 err c mN09 cases
row N10 err c mN10 cases
row N12 err c mN12 cases
row N13 err c mN13 cases
row N15 err c mN15 cases
row N16 err c mN16 cases
row N17 err c mN17 cases
