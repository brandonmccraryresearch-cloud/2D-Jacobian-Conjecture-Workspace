"""
mk_msolve.py -- write the same system (from mk_singular.polys_for) in msolve input format.
usage: python3 mk_msolve.py CHAR NORMALIZE ZVERTS OUT.ms
"""
import sys
from mk_singular import polys_for

char = int(sys.argv[1])
norm = [] if sys.argv[2] == "none" else sys.argv[2].split(",")
zv = [] if sys.argv[3] == "none" else sys.argv[3].split(",")
allv, polys = polys_for(norm, zv)
with open(sys.argv[4], "w") as f:
    f.write(",".join(allv) + "\n")
    f.write(f"{char}\n")
    f.write(",\n".join(p.replace("+(-", "-(").replace("(", "").replace(")", "") for p in polys) + "\n")
