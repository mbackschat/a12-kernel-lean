# SG9 plain and fixed per-row reads on carriers other than a Number field read, run on
# StarBinding3_DM (no index) and StarBinding4_DM (Batches index-keyed); an undeclared group
# defaults to the target's own /Probe/Out.
field free /Probe/Out/Free
field frees /Probe/Out/FreeS
group batches /Probe/Batches
op len Length(/Probe/Batches/BFreeS)
op fvn FieldValueAsNumber(/Probe/Batches/BFreeS)
op lendeep Length(Boxes/Name)
op scopy [/Probe/Batches/BFreeS]
op scat "x" + [/Probe/Batches/BFreeS]
op sfvs FieldValueAsString(/Probe/Batches/BW)
op sdeep [Boxes/Name]
op sself [/Probe/Out/FreeS] + [/Probe/Batches/BFreeS]
op sselfrev [/Probe/Batches/BFreeS] + [/Probe/Out/FreeS]
op grep NumberOfFilledGroups(/Probe/Batches, /Probe/Out)
op grepin NumberOfFilledGroups(Boxes, /Probe/Out)
comp nlenhb free len batches
comp nlenout free len
comp nfvnhb free fvn batches
comp nfvnout free fvn
comp nlendeephb free lendeep batches
comp scopyhb frees scopy batches
comp scopyout frees scopy
comp scathb frees scat batches
comp scatout frees scat
comp sfvshb frees sfvs batches
comp sfvsout frees sfvs
comp sdeephb frees sdeep batches
comp sselfhb frees sself batches
comp sselfrevhb frees sselfrev batches
comp grephb free grep batches
comp grepout free grep
comp grepinhb free grepin batches
