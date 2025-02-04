L1 = ["barnes", "cfrac", "espresso", "gs", "lean", "redis", "larson", "larson-sized", "lua", "z3"]
L2 = ["alloc-test", "cscratch", "cthrash", "glibc-simple", "glibc-thread", "lean-mathlib", "malloc-large", "mleak", "mstress", "rbstress", "rocksdb", "rptest", "sh6bench", "sh8bench", "xmalloc-test"]
L = L1+L2

dir = "hists2"

for e in L:
  print("time stap log.stp -c \"bash ../../bench.sh sys "+e+"\" &> "+dir+"/"+e+".txt")
