"""gen_kbench.py -- two kernel micro-benchmarks behind README.md's "why packed": the cost of scalar arithmetic in the
Lean kernel, and the cost of data written as list literals.
  loop N : runK 32003 N = V   -- N iterations of a Nat.rec loop (two LCG updates and one multiply-accumulate mod p)
  list N : dotK 32003 (d0 ++ ... ++ d9) = V   -- a dot product of N pairs of residues given as 10 list literals
V is computed here, so each statement is true; the kernel proves it with `decide +kernel`.
usage: python3 gen_kbench.py OUTDIR loop|list N
"""
import sys, os, random

OUT, kind, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
p = 32003
os.makedirs(OUT, exist_ok=True)
head = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n"
if kind == "loop":
    a, b, acc = 1, 2, 0
    for _ in range(N):
        a2, b2 = (a * 1103515245 + 12345) % p, (b * 69069 + 1) % p
        a, b, acc = a2, b2, (acc + a2 * b2) % p
    text = head + f"""/-- one step of two linear congruential generators and a dot-product accumulator, all mod p -/
def stepK (p : Nat) (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((st.1 * 1103515245 + 12345) % p, (st.2.1 * 69069 + 1) % p,
   (st.2.2 + ((st.1 * 1103515245 + 12345) % p) * ((st.2.1 * 69069 + 1) % p)) % p)

def runK (p n : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat × Nat) (1, 2, 0) (fun _ st => stepK p st) n).2.2

theorem bench : runK {p} {N} = {acc} := by decide +kernel
"""
elif kind == "list":
    rng = random.Random(20261006 + N)
    pairs = [(rng.randrange(p), rng.randrange(p)) for _ in range(N)]
    acc = sum(x * y for x, y in pairs) % p
    parts = [pairs[k * N // 10:(k + 1) * N // 10] for k in range(10)]
    text = head + "".join(f"def d{k} : List (Nat × Nat) := [" + ", ".join(f"({x}, {y})" for x, y in part) + "]\n"
                          for k, part in enumerate(parts))
    text += f"""
noncomputable def dotK (p : Nat) (l : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun ab _ ih => (ih + ab.1 * ab.2) % p) l

theorem bench2 : dotK {p} ({' ++ '.join(f'd{k}' for k in range(10))}) = {acc} := by decide +kernel
"""
else:
    raise SystemExit("kind must be loop or list")
name = f"kbench_{kind}_{N}.lean"
open(os.path.join(OUT, name), "w").write(text)
print(name)
