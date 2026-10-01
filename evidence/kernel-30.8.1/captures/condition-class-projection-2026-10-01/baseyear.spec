# Point-in-time sites on the plain rule comparison, 2026-10-01.
field err /Order/Note2
group root /Order
msg m Check.
cond B01 FieldFilled(Note2) And [/Order/At] == BaseYear
cond B02 FieldFilled(Note2) And [/Order/Due] == BaseYear
cond B03 FieldFilled(Note2) And [/Order/Qty] == BaseYear
cond B04 FieldFilled(Note2) And [/Order/Flag] == BaseYear
cond B05 FieldFilled(Note2) And [/Order/Note] == BaseYear
cond B06 FieldFilled(Note2) And [/Order/Amount] == BaseYear
cond B07 FieldFilled(Note2) And BaseYear == [/Order/Stamp]
cond B08 FieldFilled(Note2) And [/Order/Signed] == BaseYear
cond B09 FieldFilled(Note2) And [/Order/Window] == BaseYear
row B01 err B01 m root
row B02 err B02 m root
row B03 err B03 m root
row B04 err B04 m root
row B05 err B05 m root
row B06 err B06 m root
row B07 err B07 m root
row B08 err B08 m root
row B09 err B09 m root
