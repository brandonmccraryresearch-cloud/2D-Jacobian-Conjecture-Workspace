import lower_c as lc
import make_cert_c as mc
def digits(a): return max(len(str(a[i].p)) + len(str(a[i].q)) for i in range(5))
def lvars(letter, k, lo, hi): return [f"{letter}_{i}_{2*i-k}" for i in range(lo, hi + 1)]
groups = {"z(E4)": mc.zsub, "x(E3)": mc.xsub, "y(E2)": mc.ysub, "v(E1)": lc.vsub}
for lay, U in (("u0(E0)", lvars("a", -3, 0, 5) + lvars("b", -2, 0, 10)), ("u-1(E-1)", lvars("a", -4, 0, 4) + lvars("b", -3, 0, 9))):
    groups[lay] = {v: lc.sub[v] for v in U}
for g, d in groups.items():
    print(f"{g}: {len(d)} vars, max terms {max(len(p) for p in d.values())}, max digits {max(max(digits(c) for c in p.values()) for p in d.values() if p)}")
# expanded size of raw E_{-2} equations under substitution
def P_len(v): return len(lc.sub.get(v, {((v,1),): 1})) if v not in mc.top else 1
for W, name in ((1, "E0"), (2, "E-1"), (3, "E-2")):
    tot = []
    for k in mc.blocks[W]:
        s = 0
        for c, pv, qv in mc.eqsc[k]:
            s += P_len(pv) * P_len(qv)
        tot.append(s)
    print(f"{name}: raw equations {len(tot)}, expanded bilinear-term products per equation: max {max(tot)}, total {sum(tot)}")
