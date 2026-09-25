#!/usr/bin/env bash
# run_all.sh -- reproduce every result of LOG.md from a clean copy of scripts/.
# Requirements: Singular 4.3.x, Macaulay2 1.22, msolve 0.6.5, PARI/GP 2.15, python3 with
# sympy and python-flint.  Wall time on 4 cores: ~1 h (Macaulay2 step dominates).
# Usage:  bash run_all.sh [--skip-m2]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
RUN="$HERE/run_$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$RUN/outputs"
cp "$HERE"/scripts/* "$RUN/"
cd "$RUN"
O=outputs
step() { echo "== $1"; shift; ( "$@" ) > "$O/$LOGNAME_" 2>&1; echo "   exit=$? -> $O/$LOGNAME_"; tail -2 "$O/$LOGNAME_"; }
{
  echo "run dir: $RUN"; date -u; uname -a; python3 --version
  python3 -c "import sympy, flint; print('sympy', sympy.__version__, 'python-flint', flint.__version__)"
  Singular --version 2>&1 | head -1; M2 --version; dpkg -l msolve pari-gp 2>/dev/null | grep ^ii
} > $O/00_environment.txt 2>&1

LOGNAME_=01_gen_system.txt        step "lattice points / system size"      python3 gen_system.py
LOGNAME_=02_weights.txt           step "weight blocks"                      python3 weights.py
LOGNAME_=03_identities.txt        step "symbolic identities (I1)-(I5)"      python3 verify_identities.py
LOGNAME_=04_belyi_count.txt       step "Frobenius/Murnaghan-Nakayama count" python3 belyi_count.py
LOGNAME_=05_cert_singular_p32003.txt     step "certificate, Singular, p=32003"     python3 cert_fibers_singular.py 32003
LOGNAME_=06_cert_singular_p536870909.txt step "certificate, Singular, p=536870909" python3 cert_fibers_singular.py 536870909
LOGNAME_=07_planted_controls.txt  step "planted / negative controls"       python3 planted_control.py 32003 1

# E5 lex bases modulo 124 primes near 2^31 (for the candidate quintic R and the explicit K5 data)
mkdir -p e5mod
python3 -c "
import sympy
ps=[]; q=2**31-1
while len(ps)<124:
    q=sympy.prevprime(q); ps.append(q)
print('\n'.join(map(str,ps)))" > primes.txt
echo "== E5 lex bases mod 124 primes"
xargs -P 3 -I{} sh -c 'python3 e5_lex_modp.py {} e5mod/p{}.json > e5mod/p{}.log 2>&1' < primes.txt
ls e5mod/*.json | wc -l > $O/08_e5mod_count.txt
LOGNAME_=09_make_R.txt            step "candidate quintic R (CRT)"         python3 make_R_cand.py
gp -q --default parisizemax=2000000000 psi.gp < /dev/null 2>&1 | grep -E "^(RR|PSI|CHECK)" > psi.out
cp psi.out $O/10_psi.txt
echo 'read("R_cand.gp"); Rz = R*denominator(content(R)); print("irreducible: ", polisirreducible(Rz)); Rr = polredabs(Rz); print("polredabs: ", Rr); print("field disc: ", factor(nfdisc(Rr))); print("Galois group: ", polgalois(Rr));' > field_info.gp
gp -q --default parisizemax=2000000000 field_info.gp < /dev/null > $O/11_field_info.txt 2>&1
gp -q --default parisizemax=2000000000 find_split_prime.gp < /dev/null > $O/12_split_primes.txt 2>&1
LOGNAME_=13_e5_exact_K5.txt       step "explicit E5 solution over K5 (exact)" python3 e5_exact_K5.py
cp e5_exact_K5.json $O/
LOGNAME_=14_partial_solution.txt  step "direct bracket check of the partial solution" python3 verify_partial_solution.py
LOGNAME_=15_cert_msolve_p30011.txt step "certificate, msolve, p=30011"     python3 cert_fibers_msolve.py 30011
LOGNAME_=16_msolve_control.txt    step "msolve control"                    python3 msolve_control.py
if [ "${1:-}" != "--skip-m2" ]; then
  LOGNAME_=17_cert_m2_p32003.txt  step "certificate, Macaulay2, p=32003 (slow)" python3 cert_fibers_m2.py 32003
fi
date -u >> $O/00_environment.txt
( cd $O && md5sum * > ../outputs_MD5SUMS.txt )
echo "done: $RUN"
