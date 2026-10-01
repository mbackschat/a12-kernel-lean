# Point-in-time sites on the plain rule comparison, 2026-10-01.
field err /Order/Note2
group root /Order
msg m Check.
cond T01 FieldFilled(Note2) And [/Order/At] == Now
cond T02 FieldFilled(Note2) And Today == [/Order/At]
cond T03 FieldFilled(Note2) And Now == [/Order/Due]
cond T04 FieldFilled(Note2) And [/Order/Flag] == Today
cond T05 FieldFilled(Note2) And [/Order/Note] == Today
cond T06 FieldFilled(Note2) And [/Order/Qty] == Today
cond T07 FieldFilled(Note2) And [/Order/Flag] == Now
cond T08 FieldFilled(Note2) And [/Order/Window] == Today
cond T09 FieldFilled(Note2) And [/Order/Signed] == Now
cond T10 FieldFilled(Note2) And [/Order/Note] == Now
cond T11 FieldFilled(Note2) And [/Order/Plain] == Today
row T01 err T01 m root
row T02 err T02 m root
row T03 err T03 m root
row T04 err T04 m root
row T05 err T05 m root
row T06 err T06 m root
row T07 err T07 m root
row T08 err T08 m root
row T09 err T09 m root
row T10 err T10 m root
row T11 err T11 m root
