field amount /Idx/Rows/Amount
field total  /Idx/Total
field note   /Idx/Note
field when   /Idx/WhenDate
group rows   /Idx/Rows
msg mm Problem detected.

cond idxMismatch  [Amount] == [/Idx/Ledger/LedgerAmount]
cond idxCat       [Amount For /Idx/Labelled -> Continent] == 20
cond semBelowWild AtLeastOneFieldFilled(Outer*/Inner/InnerAmount For "1")
cond fromOutside  RepetitionNotUnique(Rows*/Amount, Outer/Inner/InnerAmount @From Outer/Inner)
cond parInvalid   NoFieldFilled(Rows*/Amount, Peers*/PeerAmount)
cond missYear     [WhenDate] != Date("1","11")
cond onlyConst    Valid(Date("01","01","1990"))
cond extractMix   [WhenDate] != Date(HoursFromTime(OtherDate),"11","2022")
cond fourParam    [WhenDate] != Date("11","11",YearFromDate(OtherDate),"89")
cond nonNumeric   [WhenDate] == AddDays(OtherDate, "text")
cond invConst     NumberOfValueInFields("20.02.2022" In Note, Note2) > 0
cond noStrEnum    NumberOfValueInFields("Berlin" In Total, Total) > 1
cond noYesNo      NumberOfValueInFields(True In Note, Note2) > 1
cond badCatVal    FieldValueIncludedInValueList(Labelled -> Continent, "NotAContinent")
cond rangeStr     [Note] == RangeAsString(Total, 2, 4)
cond calcNonNum   [Note] * 4 == 7
cond enumCmp      [Labelled] == [Plain]
cond sopTwo       SumOfProducts(Rows*/Amount, Peers*/PeerAmount) >= 100

row D01 amount idxMismatch  mm rows
row D02 amount idxCat       mm rows
row D03 total  semBelowWild mm
row D04 total  fromOutside  mm
row D05 total  parInvalid   mm
row D06 when   missYear     mm
row D07 when   onlyConst    mm
row D08 when   extractMix   mm
row D09 when   fourParam    mm
row D10 when   nonNumeric   mm
row D11 note   invConst     mm
row D12 note   noStrEnum    mm
row D13 note   noYesNo      mm
row D14 note   badCatVal    mm
row D15 note   rangeStr     mm
row D16 note   calcNonNum   mm
row D17 note   enumCmp      mm
row D18 total  sopTwo       mm
