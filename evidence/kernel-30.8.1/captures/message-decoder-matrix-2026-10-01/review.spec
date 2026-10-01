# Cold-review settling batch for the decoder slice, 2026-10-01.
field err /Probe/Cases/Score
group cases /Probe/Cases
cond c FieldFilled(Score) And FieldFilled(Grade)
msg mF1a Check $Score For Nope/$.
msg mF1b Check $Score For Nope//x$.
msg mF1c Check $Score For Nope/%$.
msg mF1d Check $Score For /Nope/$.
msg mF1e Check $Score For Nope$.
msg mF1f Check $Score For ../Nope/$.
msg mF2a Check $#../Nope/$.
msg mF2b Check $#../Nope//x$.
msg mF2c Check $#../Nope/%$.
msg mF2d Check $#../Nope$.
msg mF3a Check $..Probe.x$.
msg mF3b Check $..Probe.x/Anchor$.
msg mF3c Check $Score For ..Probe.x$.
msg mF3d Check $#..Probe.x$.
msg mF4a Check $Grade->Nope.%$.
msg mF4b Check $Grade->Band.%$.
msg mF4c Check $Grade->Band. %$.
msg mF5a Check $#/Probe/Cases For Nope For "k"$.
msg mF5b Check $#/Probe/Cases For Score For Nope$.
msg mF5c Check $#/Probe/Cases For /Nope$.
msg mF5d Check $#/Probe/Cases For /Nope For "k"$.
msg mF5e Check $#/Probe/Cases For ../../..$.
msg mF5f Check $#/Probe/Cases For ..Wrong$.
msg mF5g Check $#/Probe/Cases For RuleGroup$.
msg mF5h Check $#/Probe/Cases For Nope$.
row F1a err c mF1a cases
row F1b err c mF1b cases
row F1c err c mF1c cases
row F1d err c mF1d cases
row F1e err c mF1e cases
row F1f err c mF1f cases
row F2a err c mF2a cases
row F2b err c mF2b cases
row F2c err c mF2c cases
row F2d err c mF2d cases
row F3a err c mF3a cases
row F3b err c mF3b cases
row F3c err c mF3c cases
row F3d err c mF3d cases
row F4a err c mF4a cases
row F4b err c mF4b cases
row F4c err c mF4c cases
row F5a err c mF5a cases
row F5b err c mF5b cases
row F5c err c mF5c cases
row F5d err c mF5d cases
row F5e err c mF5e cases
row F5f err c mF5f cases
row F5g err c mF5g cases
row F5h err c mF5h cases
