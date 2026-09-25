# F5: computation callers that name no target to their shape, and below-star placement with a target
field free /Probe/Out/Free
field rangeout /Probe/Out/RangeOut
field enumout /Probe/Out/EnumOut
group ledger /Probe/Ledger
group batches /Probe/Batches
group out /Probe/Out
op tvc NumberOfValueInFields("x" In /Probe/Batches/BText, /Probe/RootS)
op tvcall NumberOfValueInFields("x" In /Probe/Batches*/BText, /Probe/RootS)
op drffv FirstFilledValue(/Probe/Batches/BRange, /Probe/RootRange)
op drffvall FirstFilledValue(/Probe/Batches*/BRange, /Probe/RootRange)
op enffv FirstFilledValue(/Probe/Batches/BEnum, /Probe/RootEnum)
op enffvall FirstFilledValue(/Probe/Batches*/BEnum, /Probe/RootEnum)
op bgc NumberOfValueInFields(True In /Probe/Batches/Flags)
op bgcall NumberOfValueInFields(True In /Probe/Batches*/Flags)
op sop SumOfProducts(/Probe/Batches*/Items/W, /Probe/Batches*/Items/Q)
op sopall SumOfProducts(/Probe/Batches*/Items*/W, /Probe/Batches*/Items*/Q)
op anffv FirstFilledValue(/Probe/Batches*/Items/W)
op anffvall FirstFilledValue(/Probe/Batches*/Items*/W)
ccross L free tvc,tvcall,bgc,bgcall,sop,sopall,anffv,anffvall ledger
ccross B free tvc,tvcall,bgc,bgcall,sop,sopall,anffv,anffvall batches
ccross O free tvc,tvcall,bgc,bgcall,sop,sopall,anffv,anffvall out
ccross LR rangeout drffv,drffvall ledger
ccross BR rangeout drffv,drffvall batches
ccross OR rangeout drffv,drffvall out
ccross LE enumout enffv,enffvall ledger
ccross BE enumout enffv,enffvall batches
ccross OE enumout enffv,enffvall out
