field amount   /Idx/Rows/Amount
field total    /Idx/Total
field inner    /Idx/Outer/Inner/InnerAmount

msg m Problem here.

cond nestedIdx    FieldFilled(Rows/Amount for Peers/PeerAmount for Ledger/LedgerNote)
cond idxCategory  [Rows/Amount for Country -> Continent] == 20
cond idxWildcard  AtLeastOneFieldFilled(Outer*/Inner/InnerAmount for "1")
cond idxTypeBad   FieldFilled(Rows/Amount for Ledger/LedgerNote)
cond idxTypeOk    FieldFilled(Rows/Amount for Peers/PeerAmount)
cond idxLiteral   FieldFilled(Rows/Amount for "1")
cond parIter      RepetitionNotUnique(Rows*/Amount) And GroupsNotCollectivelyFilled(Rows, Peers)
cond parInvalid   NoFieldFilled(Rows/Amount, Peers*/PeerAmount)
cond crossGroups  [Rows/Amount] == [Peers/PeerAmount]
cond crossLedger  [Rows/Amount] == [Ledger/LedgerNote]
cond sopArity     SumOfProducts(Rows*/Amount) >= 100
cond sopThree     SumOfProducts(Rows*/Amount, Peers*/PeerAmount, Ledger*/LedgerNote) >= 100
cond dottedPath   FieldFilled(Rows.*/Amount)
cond notInRule    RepetitionNotUnique(Total, Rows/Amount)
cond fromOutside  RepetitionNotUnique(Total, Outer/Inner/InnerAmount @From Outer/Inner)
cond innerWild    AtLeastOneFieldFilled(Outer*/Inner*/InnerAmount)
cond deepIdx      FieldFilled(Outer/Inner/InnerAmount for Rows/Amount)

row A01 total nestedIdx m
row A02 total idxCategory m
row A03 total idxWildcard m
row A04 total idxTypeBad m
row A05 total idxTypeOk m
row A06 total idxLiteral m
row A07 total parIter m
row A08 total parInvalid m
row A09 total crossGroups m
row A10 total crossLedger m
row A11 total sopArity m
row A12 total sopThree m
row A13 total dottedPath m
row A14 total notInRule m
row A15 total fromOutside m
row A16 total innerWild m
row A17 total deepIdx m
row A18 amount nestedIdx m
row A19 amount parIter m
row A20 inner idxWildcard m
