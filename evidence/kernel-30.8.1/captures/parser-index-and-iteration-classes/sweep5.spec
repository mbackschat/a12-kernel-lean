field total  /Idx/Total
field amount /Idx/Rows/Amount
group rows   /Idx/Rows

cond ok        FieldFilled(Total)
cond bad       FieldFilled(
cond starRows  AtLeastOneFieldFilled(Rows*/Amount)

msg plain    Nothing special.
msg badParam Text $BadToken@@@$ here.
msg grpLine  Text $Rows.Vordruckzeile$ here.
msg grpName  Text $Rows.Vordruckname$ here.
msg fieldRef Text $Total$ here.
msg groupPos Row $#Rows$ is wrong.
msg emptyPar Text $$ here.
msg unclosed Text $Total here.

row E01 total  ok       badParam
row E02 total  ok       grpLine
row E03 total  ok       grpName
row E04 total  bad      fieldRef
row E05 total  starRows groupPos
row E06 total  ok       emptyPar
row E07 total  ok       unclosed
row E08 amount starRows groupPos rows
row E09 total  ok       fieldRef
