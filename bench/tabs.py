import re
import sys
import collections
from scipy.stats import gmean

#try:
#    import pygal
#except ImportError:
#    print('You need to install pygal.')
#    sys.exit(1)

if len(sys.argv) != 3:
    print('Usage: %s results.txt n' % sys.argv[0])
    sys.exit(1)

r = re.compile('^([^ ]+) +([^ ]+) +([0-9:.]+) +([0-9]+)')

import math

# x = 0 => time
# x = 1 => RSS
def f(time_or_rss):
    allocs = collections.defaultdict(lambda: collections.defaultdict(dict))
    # necesserary 0 or 1
    if time_or_rss != 0 and time_or_rss != 1:
        assert(False)
    # parsing the file
    # all data related to the test test_name with the alloc alloc_name
    # is put into alloc[test_name][alloc_name]
    with open(sys.argv[1]) as f:
        for l in f.readlines():
            match = r.search(l)
            if not match:
                continue
            test_name = match.group(1)
            alloc_name = match.group(2)
            time_split = match.group(3).split(':')
            rss = match.group(4)
            rss = int(rss)
            time_taken = 0
            if len(time_split) == 2:
                time_taken = int(time_split[0]) * 60 + float(time_split[1])
            else:
                time_taken = float(time_split[0])
            data = None
            if time_or_rss == 0:
                data = time_taken
            else:
                data = rss
            if alloc_name in allocs[test_name].keys():
                allocs[test_name][alloc_name].append(data)
            else:
                allocs[test_name][alloc_name] = [data]

    # computing geometry mean of execution time/RSS for a given test with a given alloc on all runs
    # all data related to the test test_name with the alloc alloc_name
    # is put into allocs_[test_name][alloc_name]
    n = int(sys.argv[2])
    allocs_ = collections.defaultdict(lambda: collections.defaultdict(dict))
    for test in allocs.keys():
        for alloc in allocs[test].keys():
            #print(test, alloc)
            assert(len(allocs[test][alloc]) == int(sys.argv[2]))
            #print(allocs[test][alloc])
            gm = gmean(allocs[test][alloc])
            #gm = round(gm, 4)
            allocs_[test][alloc] = gm
            #print(gm)

    # computing overhead of execution time/RSS with respect to hm, used as a baseline
    for test_name, results in allocs_.items():
        #line_chart = pygal.Bar(logarithmic=True)
        #line_chart.title = test_name + ' (in seconds)'
        x = []
        y = []
        b = 0
        #v_st = 0
        #v_hm = 0
        for k, t in results.items():
            if k == "hm":
                b = t
        if b == 0:
            b = 1
        for k, t in results.items():
            #if k == "sys":
            #    continue
            x.append(k)
            y.append(t/b)
        allocs_[test_name]["x"] = x
        allocs_[test_name]["y"] = y
        allocs_[test_name]["base"] = b
        for i in range(len(x)):
            allocs_[test_name][x[i]] = y[i]

    # putting normalized geometric mean into allocs_mean
    allocs_mean = collections.defaultdict(lambda: collections.defaultdict(dict))
    for k in allocs_["cfrac"]["x"]:
        allocs_mean[k] = []
    for test_name in allocs_.keys():
        for i in range(len(allocs_[test_name]["x"])):
            if k not in [ "x", "base", "base", "y"]:
                key = allocs_[test_name]["x"][i]
                value = allocs_[test_name]["y"][i]
                if round(value, 2) > 0:
                    allocs_mean[key].append(value)

    # computing geometric mean of overhead for a given malloc on all tests wrt hm
    allocs_min = {}
    allocs_max = {}
    allocs_mean2 = {}
    for k in allocs_mean.keys():
        minimum = 1000
        maximum = 0
        for v in allocs_mean[k]:
            if v < minimum:
                minimum = v
            if v > maximum:
                maximum = v
        allocs_mean2[k] = gmean(allocs_mean[k])
        allocs_min[k] = minimum
        allocs_max[k] = maximum
    #print(allocs_mean2)



    n = len(allocs_.items())
    #print (n)
    
    s = ""
    #if time_or_rss == 0:
    #    s += "Time.\n"
    #else:
    #    s += "RSS.\n"
    
    nb_allocs = 0
    for k in results.items():
        if k[0] not in [ "x", "y", "base" ]:
            nb_allocs += 1
    s += "\\begin{tabular}{l"
    for k in range(nb_allocs):
        s += "|r"
    s += "}\n"
    s += "Benchmark"
    s += " & \\textbf{st} & hm"
    for k in results.items():
        if k[0] not in [ "x", "y", "base", "st", "hm" ]:
            if k[0] == "sys":
                s += " & glibc"
            else:
                s += " & "+str(k[0])
    s += "\\\\\n\\hline\n"

    for k in ["barnes", "cfrac", "espresso", "gs", "larsonN", "larsonN-sized", "leanN", "linux", "lua", "mathlib", "redis", "rocksdb", "z3"]:
        s += k
        #print(k, allocs_[k]["st"])
        s += " & \\textbf{"+str(round(allocs_[k]["st"], 2)).ljust(4, '0')+"}"
        s += " & "+str(round(allocs_[k]["hm"], 2)).ljust(4, '0')
        for k2 in results.items():
            if k2[0] not in [ "x", "y", "base", "st", "hm" ]:
                s += " & "+str(round(allocs_[k][k2[0]], 2)).ljust(4, '0')
        s += "\\\\\n"
    s += "\\hline\n"
    for k in ["alloc-test1", "alloc-testN", "cache-scratch1", "cache-scratchN", "cache-thrash1", "cache-thrashN", "glibc-simple", "glibc-thread", "malloc-large", "mleak10", "mleak100", "mstressN", "rbstress1", "rbstressN", "rptestN", "sh6benchN", "sh8benchN", "xmalloc-testN"]:
        s += k
        s += " & \\textbf{"+str(round(allocs_[k]["st"], 2)).ljust(4, '0')+"}"
        s += " & "+str(round(allocs_[k]["hm"], 2)).ljust(4, '0')
        for k2 in results.items():
            if k2[0] not in [ "x", "y", "base", "st", "hm" ]:
                s += " & "+str(round(allocs_[k][k2[0]], 2)).ljust(4, '0')
        s += "\\\\\n"
    s += "\\hline\n"

    s += "gmean"
    s += " & \\textbf{"+str(round(allocs_mean2["st"], 2)).ljust(4, '0')+"}"
    s += " & "+str(round(allocs_mean2["hm"], 2)).ljust(4, '0')
    for k in allocs_["cfrac"]["x"]:
        res = allocs_mean2[k]
        if k not in [ "hm", "st" ]:
            s += " & "+str(round(res, 2)).ljust(4, '0')
    s += "\\\\\n"

    s += "min"
    s += " & \\textbf{"+str(round(allocs_min["st"], 2)).ljust(4, '0')+"}"
    s += " & "+str(round(allocs_min["hm"], 2)).ljust(4, '0')
    for k in allocs_["cfrac"]["x"]:
        res = allocs_min[k]
        if k not in [ "hm", "st" ]:
            s += " & "+str(round(res, 2)).ljust(4, '0')
    s += "\\\\\n"

    s += "max"
    s += " & \\textbf{"+str(round(allocs_max["st"], 2)).ljust(4, '0')+"}"
    s += " & "+str(round(allocs_max["hm"], 2)).ljust(4, '0')
    for k in allocs_["cfrac"]["x"]:
        res = allocs_max[k]
        if k not in [ "hm", "st" ]:
            s += " & "+str(round(res, 2)).ljust(4, '0')
    s += "\\\\\n"

    s += "\\end{tabular}\n"
    return s

def as_document(s, label):
    s2 = ""
    s2 += "\\documentclass[a4paper, twoside, 12pt]{article}\n"
    s2 += "\\usepackage[margin=2cm]{geometry}\n"
    s2 += "\\begin{document}\n"
    s2 += label
    s2 += "\\begin{center}\n"
    s2 += s
    s2 += "\\end{center}\n"
    s2 += "\\end{document}\n"
    return s2

s_time = f(0)
s_rss = f(1)

n = int(sys.argv[2])

with open('tabular-time.tex', 'w') as f:
    f.write(as_document(s_time, "Execution time, using hardened\\_malloc as a baseline, geometric mean of "+str(n)+" runs."))
with open('tabular-rss.tex', 'w') as f:
    f.write(as_document(s_rss, "RSS, using hardened\\_malloc as a baseline, geometric mean of "+str(n)+" runs."))
