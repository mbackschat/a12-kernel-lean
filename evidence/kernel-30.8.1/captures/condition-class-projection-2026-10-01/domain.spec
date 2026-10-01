# Projection-domain rows, 2026-10-01: point partners on the left, the End endpoint beyond Signed and Plain, and Length off the measured operator and kinds.
field err /Order/Note2
group root /Order
msg m Check.
cond D01 FieldFilled(Note2) And BaseYear == [/Order/Note]
cond D02 FieldFilled(Note2) And BaseYear == [/Order/Window]
cond D03 FieldFilled(Note2) And BaseYear == [/Order/Flag]
cond D04 FieldFilled(Note2) And Today == [/Order/Note]
cond D05 FieldFilled(Note2) And Today == [/Order/Flag]
cond D06 FieldFilled(Note2) And Today == [/Order/Qty]
cond D07 FieldFilled(Note2) And Now == [/Order/Qty]
cond D08 FieldFilled(Note2) And Now == [/Order/Plain]
cond D09 FieldFilled(Note2) And StartOfDateRange(BaseYear) == [/Order/Qty]
cond E01 FieldFilled(Note2) And [/Order/Note] == EndOfDateRange(BaseYear)
cond E02 FieldFilled(Note2) And [/Order/Qty] == EndOfDateRange(BaseYear)
cond E03 FieldFilled(Note2) And [/Order/Flag] == EndOfDateRange(BaseYear)
cond E04 FieldFilled(Note2) And [/Order/Window] == EndOfDateRange(BaseYear)
cond E05 FieldFilled(Note2) And [/Order/Due] == EndOfDateRange(BaseYear)
cond E06 FieldFilled(Note2) And [/Order/At] == EndOfDateRange(BaseYear)
cond L01 FieldFilled(Note2) And Length(/Order/Qty) == 2
cond L02 FieldFilled(Note2) And Length(/Order/Flag) > 2
cond L03 FieldFilled(Note2) And Length(/Order/Plain) > 2
cond L04 FieldFilled(Note2) And Length(/Order/Window) > 2
row D01 err D01 m root
row D02 err D02 m root
row D03 err D03 m root
row D04 err D04 m root
row D05 err D05 m root
row D06 err D06 m root
row D07 err D07 m root
row D08 err D08 m root
row D09 err D09 m root
row E01 err E01 m root
row E02 err E02 m root
row E03 err E03 m root
row E04 err E04 m root
row E05 err E05 m root
row E06 err E06 m root
row L01 err L01 m root
row L02 err L02 m root
row L03 err L03 m root
row L04 err L04 m root
