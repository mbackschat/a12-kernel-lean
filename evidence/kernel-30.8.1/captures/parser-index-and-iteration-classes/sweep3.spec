field amount   /Idx/Rows/Amount
field inner    /Idx/Outer/Inner/InnerAmount
field total    /Idx/Total

group rows     /Idx/Rows
group innerG   /Idx/Outer/Inner

msg mm Problem detected.

cond nestedIdx    FieldFilled(Amount For Peers/PeerAmount For Ledger/LedgerNote)
cond idxCategory  [Amount For Country -> Continent] == 20
cond idxTypeBad   FieldFilled(Amount For Ledger/LedgerNote)
cond idxTypeOk    FieldFilled(Amount For Peers/PeerAmount)
cond idxLiteral   FieldFilled(Amount For "1")
cond crossPeers   [Amount] == [Peers/PeerAmount]
cond crossLedger  [Amount] == [Ledger/LedgerNote]
cond parStar      [Amount] == [Peers*/PeerAmount]
cond notInRule    RepetitionNotUnique(Total, Amount)
cond fromOutside  RepetitionNotUnique(Amount, Outer/Inner/InnerAmount @From Outer/Inner)
cond dotted       FieldFilled(Amount.*)
cond sopArity     SumOfProducts(Amount) >= 100
cond deepIdx      FieldFilled(InnerAmount For Rows/Amount)
cond wildIdx      AtLeastOneFieldFilled(Outer*/Inner/InnerAmount For "1")
cond selfIdx      FieldFilled(Amount For Amount)

row B01 amount nestedIdx   mm rows
row B02 amount idxCategory mm rows
row B03 amount idxTypeBad  mm rows
row B04 amount idxTypeOk   mm rows
row B05 amount idxLiteral  mm rows
row B06 amount crossPeers  mm rows
row B07 amount crossLedger mm rows
row B08 amount parStar     mm rows
row B09 amount notInRule   mm rows
row B10 amount fromOutside mm rows
row B11 amount dotted      mm rows
row B12 amount sopArity    mm rows
row B13 inner  deepIdx     mm innerG
row B14 total  wildIdx     mm
row B15 amount selfIdx     mm rows
