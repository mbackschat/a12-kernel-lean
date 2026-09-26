# Disposition grid, 2026-09-26: the count's lone-group arity by placement, the overlap In list's root gate order.
# Generate with scripts/make-probe-ops.sh disp.spec disp-ops.json; run against Disp_DM.json.
msg m plain message
group gShip /Ship
group gParcels /Ship/Parcels
group gPlain /Ship/Plain
group gMid /Ship/Mid
group gInner /Ship/Mid/Inner
group gSide /Ship/Side
group gLines /Ship/Parcels/Lines
group gLot /Lot
group gForm /Form
group gCrate /Crate
group gSlots /Crate/Slots
field fLabel /Ship/Parcels/Label
field fTag /Ship/Plain/Tag
field fCode /Ship/Mid/Inner/Code
field fQty /Ship/Parcels/Lines/Qty
field fSerial /Lot/Serial
field fTerm /Lot/Term
field fYTerm /Lot/YTerm
field fSpan /Form/Span
field fYSpan /Form/YSpan
field fMark /Crate/Mark
field fPos /Crate/Slots/Pos
field fWin /Ship/Win
cond cParcels FieldFilled(/Ship/Parcels/Label) And NumberOfFilledGroups(/Ship/Parcels) > 0
cond cPlain FieldFilled(/Ship/Plain/Tag) And NumberOfFilledGroups(/Ship/Plain) > 0
cond cInner FieldFilled(/Ship/Mid/Inner/Code) And NumberOfFilledGroups(/Ship/Mid/Inner) > 0
cond cLines FieldFilled(/Ship/Parcels/Lines/Qty) And NumberOfFilledGroups(/Ship/Parcels/Lines) > 0
cond cLot FieldFilled(/Lot/Serial) And NumberOfFilledGroups(/Lot) > 0
cond cCrate FieldFilled(/Crate/Mark) And NumberOfFilledGroups(/Crate) > 0
cond cSlots FieldFilled(/Crate/Slots/Pos) And NumberOfFilledGroups(/Crate/Slots) > 0
cond oTerm FieldFilled(Term) And AtLeastOneDateRangeOverlaps(Term In /Lot*)
cond oYTerm FieldFilled(YTerm) And AtLeastOneDateRangeOverlaps(YTerm In /Lot*)
cond oTermBoth FieldFilled(Term) And AtLeastOneDateRangeOverlaps(Term In Term, /Lot*)
cond oSpan FieldFilled(Span) And AtLeastOneDateRangeOverlaps(Span In /Form)
cond oYSpan FieldFilled(YSpan) And AtLeastOneDateRangeOverlaps(YSpan In /Form)
cond oTermSerial FieldFilled(Term) And AtLeastOneDateRangeOverlaps(Term In Term, Serial)
cond oSerial FieldFilled(Term) And AtLeastOneDateRangeOverlaps(Term In Serial)
cond oSerialTwice FieldFilled(Term) And AtLeastOneDateRangeOverlaps(Term In Serial, Serial)
cond oWin FieldFilled(Win) And AtLeastOneDateRangeOverlaps(Win In /Form)
row c1 fLabel cParcels m gParcels
row c2 fLabel cParcels m gShip
row c3 fTag cPlain m gPlain
row c4 fTag cPlain m gShip
row c5 fCode cInner m gInner
row c6 fCode cInner m gMid
row c7 fCode cInner m gShip
row c8 fTag cPlain m gSide
row c9 fQty cLines m gLines
row c11 fSerial cLot m gLot
row c12 fMark cCrate m gCrate
row c13 fPos cSlots m gCrate
row c14 fQty cLines m gParcels
row c15 fPos cSlots m gSlots
row o1 fTerm oTerm m gLot
row o2 fYTerm oYTerm m gLot
row o3 fTerm oTermBoth m gLot
row o4 fSpan oSpan m gForm
row o5 fYSpan oYSpan m gForm
row o6 fWin oWin m gShip
row o7 fTerm oTermSerial m gLot
row o8 fTerm oSerial m gLot
row o9 fTerm oSerialTwice m gLot
