# Cold-review reproduction batch for b21acde4 on StarBinding3_DM
field free /Probe/Out/Free
field amt2 /Probe/Batches/Boxes/Amt2
field bw /Probe/Batches/BW
field w /Probe/W
group batches /Probe/Batches
group boxes /Probe/Batches/Boxes
group probe /Probe
op selfFirst [/Probe/Out/Free] + Sum(Boxes*/Amt)
op selfLast Sum(Boxes*/Amt) + [/Probe/Out/Free]
op selfPlain [/Probe/Out/Free] + [BW]
op dupAfter Sum(/Probe/Batches/Boxes*/Amt, /Probe/W, /Probe/W)
op dupBefore Sum(/Probe/W, /Probe/W, /Probe/Batches/Boxes*/Amt)
op dupOnly Sum(/Probe/W, /Probe/W)
op innerBound Sum(/Probe/Batches*/Boxes/Amt)
op bothStarred Sum(/Probe/Batches*/Boxes*/Amt)
comp f4a free selfFirst batches
comp f4b free selfLast batches
comp f4c free selfPlain batches
comp f5a free dupAfter
comp f5b free dupBefore
comp f5c free dupOnly
comp f3a amt2 innerBound
comp f3b amt2 bothStarred
cond vInner Sum(/Probe/Batches*/Boxes/Amt) > 0
cond vBoth Sum(/Probe/Batches*/Boxes*/Amt) > 0
cond vGc NumberOfFilledGroups(/Probe/Batches/Boxes*/BSeal) > 0
msg m m
row r3a amt2 vInner m boxes
row r3b amt2 vBoth m boxes
row r11a bw vGc m probe
row r11b w vGc m batches
row r11c bw vGc m batches
