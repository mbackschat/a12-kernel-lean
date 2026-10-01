# Group keyword alternatives with a key, name-position walks without a name, and a lexer fault past the prediction window, 2026-10-01.
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mK01 Check $#RootGroup For "k"$.
msg mK02 Check $#RuleGroup For "k"$.
msg mK03 Check $#Zeile For "k"$.
msg mK04 Check $#RuleGroup For$.
msg mK05 Check $#/Probe/Cases For "k" x$.
msg mK06 Check $#/Probe/Cases For Score/$.
msg mK07 Check $#/Probe/Cases For Nope/x$.
msg mU01 Check $..$.
msg mU02 Check $..Probe$.
msg mU03 Check $..Nope$.
msg mU04 Check $../..$.
msg mX01 Check $Nope For é$.
msg mX02 Check $Grade->Nope é$.
msg mX03 Check $Nope é$.
row K01 err c mK01 cases
row K02 err c mK02 cases
row K03 err c mK03 cases
row K04 err c mK04 cases
row K05 err c mK05 cases
row K06 err c mK06 cases
row K07 err c mK07 cases
row U01 err c mU01 cases
row U02 err c mU02 cases
row U03 err c mU03 cases
row U04 err c mU04 cases
row X01 err c mX01 cases
row X02 err c mX02 cases
row X03 err c mX03 cases
