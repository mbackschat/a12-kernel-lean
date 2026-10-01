# Base-year range endpoints on the plain rule comparison, 2026-10-01.
field err /Order/Note2
group root /Order
msg m Check.
cond R01 FieldFilled(Note2) And [/Order/Note] == StartOfDateRange(BaseYear)
cond R02 FieldFilled(Note2) And [/Order/Qty] == StartOfDateRange(BaseYear)
cond R03 FieldFilled(Note2) And [/Order/Flag] == StartOfDateRange(BaseYear)
cond R04 FieldFilled(Note2) And [/Order/Signed] == EndOfDateRange(BaseYear)
cond R05 FieldFilled(Note2) And [/Order/Window] == StartOfDateRange(BaseYear)
cond R06 FieldFilled(Note2) And [/Order/Due] == StartOfDateRange(BaseYear)
cond R07 FieldFilled(Note2) And [/Order/At] == StartOfDateRange(BaseYear)
cond R08 FieldFilled(Note2) And [/Order/Plain] == EndOfDateRange(BaseYear)
row R01 err R01 m root
row R02 err R02 m root
row R03 err R03 m root
row R04 err R04 m root
row R05 err R05 m root
row R06 err R06 m root
row R07 err R07 m root
row R08 err R08 m root
