field root /Probe/SkuText
field row /Probe/Rows/RowText
field out /Probe/Amount
field rowOut /Probe/Rows/Sub/Leaf
group host /Probe
msg none Probe
cond plain FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] < 1) == 0
cond plainRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] < 1) == 0
op plain Sum(Rows*/RowVal Having [Rows/RowVal] < 1)
row vRootplain root plain none host
row vRowplain row plainRow none host
comp cRootplain out plain host
comp cRowplain rowOut plain host
cond dateLeft FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowVal]) == 0
cond dateLeftRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowVal]) == 0
op dateLeft Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowVal])
row vRootdateLeft root dateLeft none host
row vRowdateLeft row dateLeftRow none host
comp cRootdateLeft out dateLeft host
comp cRowdateLeft rowOut dateLeft host
cond dateRight FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowDate]) == 0
cond dateRightRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowDate]) == 0
op dateRight Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowDate])
row vRootdateRight root dateRight none host
row vRowdateRight row dateRightRow none host
comp cRootdateRight out dateRight host
comp cRowdateRight rowOut dateRight host
cond dateTwin FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowDate]) == 0
cond dateTwinRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowDate]) == 0
op dateTwin Sum(Rows*/RowVal Having [Rows/RowDate] < [Rows/RowDate])
row vRootdateTwin root dateTwin none host
row vRowdateTwin row dateTwinRow none host
comp cRootdateTwin out dateTwin host
comp cRowdateTwin rowOut dateTwin host
cond scale FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] == [Rows/RowScaled]) == 0
cond scaleRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] == [Rows/RowScaled]) == 0
op scale Sum(Rows*/RowVal Having [Rows/RowVal] == [Rows/RowScaled])
row vRootscale root scale none host
row vRowscale row scaleRow none host
comp cRootscale out scale host
comp cRowscale rowOut scale host
cond scaleTwin FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowScaled]) == 0
cond scaleTwinRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowScaled]) == 0
op scaleTwin Sum(Rows*/RowVal Having [Rows/RowVal] < [Rows/RowScaled])
row vRootscaleTwin root scaleTwin none host
row vRowscaleTwin row scaleTwinRow none host
comp cRootscaleTwin out scaleTwin host
comp cRowscaleTwin rowOut scaleTwin host
cond other FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0) == 0
cond otherRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0) == 0
op other Sum(Rows*/RowVal Having [Other/OtherVal] > 0)
row vRootother root other none host
row vRowother row otherRow none host
comp cRootother out other host
comp cRowother rowOut other host
cond captureOther FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0) == 0
cond captureOtherRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0) == 0
op captureOther Sum(Rows*/RowVal Having [$Other/OtherVal] > 0)
row vRootcaptureOther root captureOther none host
row vRowcaptureOther row captureOtherRow none host
comp cRootcaptureOther out captureOther host
comp cRowcaptureOther rowOut captureOther host
cond captureRow FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Rows/RowVal] > 0) == 0
cond captureRowRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Rows/RowVal] > 0) == 0
op captureRow Sum(Rows*/RowVal Having [$Rows/RowVal] > 0)
row vRootcaptureRow root captureRow none host
row vRowcaptureRow row captureRowRow none host
comp cRootcaptureRow out captureRow host
comp cRowcaptureRow rowOut captureRow host
cond captureScale FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Rows/RowVal] == [Rows/RowScaled]) == 0
cond captureScaleRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Rows/RowVal] == [Rows/RowScaled]) == 0
op captureScale Sum(Rows*/RowVal Having [$Rows/RowVal] == [Rows/RowScaled])
row vRootcaptureScale root captureScale none host
row vRowcaptureScale row captureScaleRow none host
comp cRootcaptureScale out captureScale host
comp cRowcaptureScale rowOut captureScale host
cond captureKind FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Other/OtherVal] == "x") == 0
cond captureKindRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Other/OtherVal] == "x") == 0
op captureKind Sum(Rows*/RowVal Having [$Other/OtherVal] == "x")
row vRootcaptureKind root captureKind none host
row vRowcaptureKind row captureKindRow none host
comp cRootcaptureKind out captureKind host
comp cRowcaptureKind rowOut captureKind host
cond captureDate FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Other/OtherVal] < [Rows/RowDate]) == 0
cond captureDateRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Other/OtherVal] < [Rows/RowDate]) == 0
op captureDate Sum(Rows*/RowVal Having [$Other/OtherVal] < [Rows/RowDate])
row vRootcaptureDate root captureDate none host
row vRowcaptureDate row captureDateRow none host
comp cRootcaptureDate out captureDate host
comp cRowcaptureDate rowOut captureDate host
cond rootOnly FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Flag] == True) == 0
cond rootOnlyRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Flag] == True) == 0
op rootOnly Sum(Rows*/RowVal Having [Flag] == True)
row vRootrootOnly root rootOnly none host
row vRowrootOnly row rootOnlyRow none host
comp cRootrootOnly out rootOnly host
comp cRowrootOnly rowOut rootOnly host
cond rootRepetition FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Flag] == True And CurrentRepetition(Rows) > 0) == 0
cond rootRepetitionRow FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Flag] == True And CurrentRepetition(Rows) > 0) == 0
op rootRepetition Sum(Rows*/RowVal Having [Flag] == True And CurrentRepetition(Rows) > 0)
row vRootrootRepetition root rootRepetition none host
row vRowrootRepetition row rootRepetitionRow none host
comp cRootrootRepetition out rootRepetition host
comp cRowrootRepetition rowOut rootRepetition host
cond offpathAnd0 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0 And [Rows/RowVal] == 1.5) == 0
cond offpathAnd0Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0 And [Rows/RowVal] == 1.5) == 0
op offpathAnd0 Sum(Rows*/RowVal Having [Other/OtherVal] > 0 And [Rows/RowVal] == 1.5)
row vRootoffpathAnd0 root offpathAnd0 none host
row vRowoffpathAnd0 row offpathAnd0Row none host
comp cRootoffpathAnd0 out offpathAnd0 host
comp cRowoffpathAnd0 rowOut offpathAnd0 host
cond offpathAnd1 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [Other/OtherVal] > 0) == 0
cond offpathAnd1Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [Other/OtherVal] > 0) == 0
op offpathAnd1 Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [Other/OtherVal] > 0)
row vRootoffpathAnd1 root offpathAnd1 none host
row vRowoffpathAnd1 row offpathAnd1Row none host
comp cRootoffpathAnd1 out offpathAnd1 host
comp cRowoffpathAnd1 rowOut offpathAnd1 host
cond captureAnd0 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 And [Rows/RowVal] == 1.5) == 0
cond captureAnd0Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 And [Rows/RowVal] == 1.5) == 0
op captureAnd0 Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 And [Rows/RowVal] == 1.5)
row vRootcaptureAnd0 root captureAnd0 none host
row vRowcaptureAnd0 row captureAnd0Row none host
comp cRootcaptureAnd0 out captureAnd0 host
comp cRowcaptureAnd0 rowOut captureAnd0 host
cond captureAnd1 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [$Other/OtherVal] > 0) == 0
cond captureAnd1Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [$Other/OtherVal] > 0) == 0
op captureAnd1 Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 And [$Other/OtherVal] > 0)
row vRootcaptureAnd1 root captureAnd1 none host
row vRowcaptureAnd1 row captureAnd1Row none host
comp cRootcaptureAnd1 out captureAnd1 host
comp cRowcaptureAnd1 rowOut captureAnd1 host
cond offpathOr0 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5) == 0
cond offpathOr0Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5) == 0
op offpathOr0 Sum(Rows*/RowVal Having [Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5)
row vRootoffpathOr0 root offpathOr0 none host
row vRowoffpathOr0 row offpathOr0Row none host
comp cRootoffpathOr0 out offpathOr0 host
comp cRowoffpathOr0 rowOut offpathOr0 host
cond offpathOr1 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [Other/OtherVal] > 0) == 0
cond offpathOr1Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [Other/OtherVal] > 0) == 0
op offpathOr1 Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [Other/OtherVal] > 0)
row vRootoffpathOr1 root offpathOr1 none host
row vRowoffpathOr1 row offpathOr1Row none host
comp cRootoffpathOr1 out offpathOr1 host
comp cRowoffpathOr1 rowOut offpathOr1 host
cond captureOr0 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5) == 0
cond captureOr0Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5) == 0
op captureOr0 Sum(Rows*/RowVal Having [$Other/OtherVal] > 0 Or [Rows/RowVal] == 1.5)
row vRootcaptureOr0 root captureOr0 none host
row vRowcaptureOr0 row captureOr0Row none host
comp cRootcaptureOr0 out captureOr0 host
comp cRowcaptureOr0 rowOut captureOr0 host
cond captureOr1 FieldFilled(SkuText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [$Other/OtherVal] > 0) == 0
cond captureOr1Row FieldFilled(Rows/RowText) And Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [$Other/OtherVal] > 0) == 0
op captureOr1 Sum(Rows*/RowVal Having [Rows/RowVal] == 1.5 Or [$Other/OtherVal] > 0)
row vRootcaptureOr1 root captureOr1 none host
row vRowcaptureOr1 row captureOr1Row none host
comp cRootcaptureOr1 out captureOr1 host
comp cRowcaptureOr1 rowOut captureOr1 host
