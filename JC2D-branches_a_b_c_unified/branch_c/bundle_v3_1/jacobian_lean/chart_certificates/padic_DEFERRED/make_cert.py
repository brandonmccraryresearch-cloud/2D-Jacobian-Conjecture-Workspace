"""Mod-p certificates for the single-prime argument (J6 = Sq, Psi, Phi1, Phi2, Theta1..3; lower_c conditions).
 (P2) Q = 0 section of the weighted cone: v^N in J6|_{Q=0} for every v in T1..R2  (so V(J6) meets {Q=0} only at 0)
 (P3) Q = 1 slice: v - NF(v) in J6|_{Q=1} for the variables v, and m^2 - NF(m^2) for the standard monomial m
      (so dim_k k[x]/(J6|_{Q=1}) <= 2).
Singular only PRODUCES the cofactors; check_cert.py verifies them without Singular."""
import json, sys, subprocess, io, contextlib, os
sys.path.insert(0, os.path.abspath("."))
with contextlib.redirect_stdout(io.StringIO()):
    from hensel_test import d, kap, red, pstr, SH, WT
six = ["Sq", "Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
X6 = SH[:6]
def script(p, w, out):
    kp = red([str(c) for c in list(kap)], p, w)
    L = [f"ring R={p},({','.join(SH)}),wp({','.join(map(str, WT))});", f"poly Sq=S2-{kp}*T2^2;"]
    for n in six[1:]: L.append(f"poly {n}={pstr(d[n], p, w)};")
    L.append(f"ideal J6={','.join(six)};")
    L.append(f'link l=":w {out}"; write(l, "{{");')
    # (P2): Q = 0
    L.append(f"ring R0={p},({','.join(X6)}),wp(1,1,2,2,3,3); map f0=R,{','.join(X6)},0; ideal I0=f0(J6); ideal G0=std(I0);")
    L.append('if (dim(G0)!=0) { print("Q=0 section NOT zero-dimensional"); quit; }')
    L.append('write(l, "\\"P2\\": [");')
    for k, v in enumerate(X6):
        L.append(f"int N=1; while (reduce({v}^N,G0)!=0) {{ N++; }}")
        L.append(f"matrix C=lift(I0,{v}^N); string s=\"\"; int i; for (i=1;i<=ncols(I0);i++) {{ s=s+\"\\\"\"+string(C[i,1])+\"\\\"\"; if (i<ncols(I0)) {{ s=s+\",\"; }} }}")
        L.append(f'write(l, "{{\\"var\\": \\"{v}\\", \\"N\\": "+string(N)+", \\"cof\\": ["+s+"]}}"+"{"," if k < 5 else ""}");')
        L.append("kill N,C,s,i;")
    L.append('write(l, "],");')
    # (P3): Q = 1
    L.append(f"ring S={p},({','.join(X6)}),dp; map f1=R,{','.join(X6)},1; ideal I1=f1(J6); ideal G1=std(I1);")
    L.append('if (dim(G1)!=0 || vdim(G1)!=2) { print("Q=1 slice: unexpected dim/vdim"); quit; }')
    L.append("ideal B=kbase(G1); poly m=B[1]; if (deg(m)==0) { m=B[2]; }")
    L.append('write(l, "\\"basis\\": [\\""+string(B[1])+"\\",\\""+string(B[2])+"\\"], \\"P3\\": [");')
    L.append(f"ideal T={','.join(X6)},m^2;")
    L.append("int j; for (j=1;j<=size(T);j++) { poly g=T[j]-reduce(T[j],G1); matrix C=lift(I1,g); string s=\"\"; int i;"
             " for (i=1;i<=ncols(I1);i++) { s=s+\"\\\"\"+string(C[i,1])+\"\\\"\"; if (i<ncols(I1)) { s=s+\",\"; } }"
             " string sep=\",\"; if (j==size(T)) { sep=\"\"; }"
             " write(l, \"{\\\"g\\\": \\\"\"+string(g)+\"\\\", \\\"cof\\\": [\"+s+\"]}\"+sep); kill g,C,s,i,sep; }")
    L.append('write(l, "]}"); close(l); print("ok"); quit;')
    return "\n".join(L)
if __name__ == "__main__":
    for p, w in [(1000003, 806739), (32003, 11147)]:
        out = f"padic/cert_p{p}_w{w}.json"
        open("padic/cert.sing", "w").write(script(p, w, out))
        r = subprocess.run(["Singular", "-q", "padic/cert.sing"], capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=1800)
        print(p, w, r.stdout.strip()[-300:], r.stderr.strip()[-600:])
        c = json.load(open(out))
        print("   P2 exponents:", [(e["var"], e["N"], sum(x.count("+") + x.count("-") + 1 for x in e["cof"] if x != "0")) for e in c["P2"]])
        print("   P3 basis:", c["basis"], " generators:", [e["g"] for e in c["P3"]])
        print("   P3 cofactor sizes (approx terms):", [sum(x.count("+") + x.count("-") + 1 for x in e["cof"] if x != "0") for e in c["P3"]])
        print("   file size:", os.path.getsize(out), "bytes")
