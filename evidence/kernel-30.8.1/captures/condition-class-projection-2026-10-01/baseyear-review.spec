# Cold-review settling rows for the BaseYear partner classes, 2026-10-01: the left position and an Enumeration partner.
field err /Order/Note2
group root /Order
msg m Check.
cond Y01 FieldFilled(Note2) And BaseYear == [/Order/At]
cond Y02 FieldFilled(Note2) And BaseYear == [/Order/Signed]
cond Y03 FieldFilled(Note2) And BaseYear == [/Order/Amount]
cond Y04 FieldFilled(Note2) And BaseYear == [/Order/Plain]
cond Y05 FieldFilled(Note2) And [/Order/Plain] == BaseYear
cond Y06 FieldFilled(Note2) And [/Order/Labelled] == BaseYear
cond Y07 FieldFilled(Note2) And BaseYear == [/Order/Due]
cond Y08 FieldFilled(Note2) And BaseYear == [/Order/Qty]
cond Y09 FieldFilled(Note2) And EndOfDateRange(BaseYear) == [/Order/Note]
cond Y10 FieldFilled(Note2) And EndOfDateRange(BaseYear) == [/Order/Qty]
cond Y11 FieldFilled(Note2) And EndOfDateRange(BaseYear) == [/Order/Plain]
cond Y12 FieldFilled(Note2) And StartOfDateRange(BaseYear) == [/Order/Plain]
cond Y13 FieldFilled(Note2) And [/Order/Plain] == StartOfDateRange(BaseYear)
cond Y14 FieldFilled(Note2) And EndOfDateRange(BaseYear) == [/Order/Due]
row Y01 err Y01 m root
row Y02 err Y02 m root
row Y03 err Y03 m root
row Y04 err Y04 m root
row Y05 err Y05 m root
row Y06 err Y06 m root
row Y07 err Y07 m root
row Y08 err Y08 m root
row Y09 err Y09 m root
row Y10 err Y10 m root
row Y11 err Y11 m root
row Y12 err Y12 m root
row Y13 err Y13 m root
row Y14 err Y14 m root
