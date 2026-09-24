# F11 and F3 rows with the error field referenced, on StarBinding3_DM
field amt2 /Probe/Batches/Boxes/Amt2
field bw /Probe/Batches/BW
field w /Probe/W
group batches /Probe/Batches
group boxes /Probe/Batches/Boxes
group probe /Probe
cond bwGc FieldFilled(/Probe/Batches/BW) And NumberOfFilledGroups(/Probe/Batches/Boxes*/BSeal) > 0
cond bwOnly FieldFilled(/Probe/Batches/BW)
cond wGc FieldFilled(/Probe/W) And NumberOfFilledGroups(/Probe/Batches/Boxes*/BSeal) > 0
cond wOnly FieldFilled(/Probe/W)
cond aInner FieldFilled(Amt2) And Sum(/Probe/Batches*/Boxes/Amt) > 0
cond aBoth FieldFilled(Amt2) And Sum(/Probe/Batches*/Boxes*/Amt) > 0
msg m m
row g1 bw bwGc m probe
row g2 bw bwOnly m probe
row g3 w wGc m batches
row g4 w wOnly m batches
row g5 amt2 aInner m boxes
row g6 amt2 aBoth m boxes
