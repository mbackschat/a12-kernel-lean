# Field-copy comparison grid, 2026-09-26: each field of /Order copied by a root computation into each twin.
# Generate with scripts/make-probe-ops.sh field-copy.spec field-copy-ops.json from this directory.
field tNote /Order/Note2
op sNote [/Order/Note]
field tQty /Order/Qty2
op sQty [/Order/Qty]
field tAmount /Order/Amount2
op sAmount [/Order/Amount]
field tDue /Order/Due2
op sDue [/Order/Due]
field tAt /Order/At2
op sAt [/Order/At]
field tWindow /Order/Window2
op sWindow [/Order/Window]
field tFlag /Order/Flag2
op sFlag [/Order/Flag]
field tSigned /Order/Signed2
op sSigned [/Order/Signed]
field tPlain /Order/Plain2
op sPlain [/Order/Plain]
field tLabelled /Order/Labelled2
op sLabelled [/Order/Labelled]
op arith [/Order/Qty] + 1
ccross g tNote,tQty,tAmount,tDue,tAt,tWindow,tFlag,tSigned,tPlain,tLabelled sNote,sQty,sAmount,sDue,sAt,sWindow,sFlag,sSigned,sPlain,sLabelled
comp ctrlArith tNote arith
field tStamp /Order/Stamp2
op sStamp [/Order/Stamp]
ccross d tStamp sNote,sQty,sAmount,sDue,sAt,sWindow,sFlag,sSigned,sPlain,sLabelled,sStamp
ccross e tNote,tQty,tAmount,tDue,tAt,tWindow,tFlag,tSigned,tPlain,tLabelled sStamp
field tWide /Order/Wide
op sSwapped [/Order/Swapped]
op sWide [/Order/Wide]
comp hConflict tLabelled sSwapped
comp hWider tPlain sWide
comp hBoth tLabelled sWide
comp hNarrower tWide sPlain
comp hSwappedString tNote sSwapped
