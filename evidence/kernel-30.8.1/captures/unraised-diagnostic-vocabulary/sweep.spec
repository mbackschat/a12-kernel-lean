# Parser static-legality sweep, batch 1. Each row aims at one untouched vk_parser class.
field total   /Idx/Total
field amount  /Idx/Rows/Amount
field peerAmt /Idx/Peers/PeerAmount
field inner   /Idx/Outer/Inner/InnerAmount
field note    /Idx/Note
field country /Idx/Country
field when    /Idx/WhenDate
field absent  /Idx/NoSuchField
field flag    /Idx/Flag

group rows    /Idx/Rows
group peers   /Idx/Peers
group outer   /Idx/Outer
group root    /Idx

cond ok         FieldFilled(Total)
cond peerRef    FieldFilled(/Idx/Peers/PeerAmount)
cond badDate    [WhenDate] != Date("31","02","2026")
cond dateConst  NumberOfValueInFields(Today In Note, Note2) > 0
cond strNum     NumberOfValueInFields("x" In Note, Total) > 0
cond enumList   FieldValueIncludedInValueList(Country, [Total])
cond boolCmp    [Flag] == [Flag2]
cond validType  Valid(Total, "IBAN")
cond semIdx     [Rows/Amount For "1"] > 0
cond semIdxSem  [Rows/Amount For [Peers/PeerAmount For "1"]] > 0
cond semIdxStar [Outer*/Inner/InnerAmount For "1"] > 0
cond semIdxCat  [Country -> Speed For "1"] == "X"
cond parallel   Sum(Rows*/Amount) > Sum(Peers*/PeerAmount)
cond parallel2  NumberOfFilledFields(Rows*/Amount, Peers*/PeerAmount) > 0
cond havingPar  NumberOfFilledFields(Rows*/Amount Having [Peers/PeerAmount] > 0) > 0
cond extractIn  [WhenDate] != Date(YearFromDate(OtherDate),"02","2026")
cond innerOk    FieldFilled(/Idx/Outer/Inner/InnerAmount)

msg plain     Nothing special.

row P01 absent  ok         plain
row P02 amount  ok         plain peers
row P03 amount  peerRef    plain rows
row P04 inner   innerOk    plain outer
row P05 total   badDate    plain
row P06 total   dateConst  plain
row P07 total   strNum     plain
row P08 total   enumList   plain
row P09 total   boolCmp    plain
row P10 total   validType  plain
row P11 total   semIdx     plain
row P12 total   semIdxSem  plain
row P13 total   semIdxStar plain
row P14 total   semIdxCat  plain
row P15 total   parallel   plain
row P16 total   parallel2  plain
row P17 total   havingPar  plain
row P18 total   extractIn  plain
