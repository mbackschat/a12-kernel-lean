field amount /Idx/Rows/Amount
group rows   /Idx/Rows
msg mm Problem detected.

cond s1 [Amount] == [Peers/PeerAmount]
cond s2 [Amount] == [/Idx/Peers/PeerAmount]
cond s3 [Amount] == [../Peers/PeerAmount]
cond s4 [Amount] == [Peers*/PeerAmount]
cond s5 [Amount] == [Idx/Peers/PeerAmount]
cond s6 FieldFilled(Peers/PeerAmount)
cond s7 FieldFilled(/Idx/Peers/PeerAmount)
cond s8 FieldFilled(Peers*/PeerAmount)

row C01 amount s1 mm rows
row C02 amount s2 mm rows
row C03 amount s3 mm rows
row C04 amount s4 mm rows
row C05 amount s5 mm rows
row C06 amount s6 mm rows
row C07 amount s7 mm rows
row C08 amount s8 mm rows
