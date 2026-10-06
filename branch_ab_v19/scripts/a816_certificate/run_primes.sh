#!/bin/bash
# run_primes.sh FIRST LAST : liftstd certificate mod the inert primes inert_primes.json[FIRST..LAST-1] (each a field F_{p^5})
cd "$(dirname "$0")"
HERE="$(pwd)"; mkdir -p modp
for p in $(python3 -c "import json,sys; print(' '.join(map(str, json.load(open('inert_primes.json'))[$1:$2])))"); do
  [ -s modp/cert_$p.txt ] && grep -q DONE modp/cert_$p.log 2>/dev/null && continue
  python3 mk_dump.py $p cert modp/dump_$p.sing
  ( cd modp && python3 "$HERE/guardrun.py" --max-anon 5200 -- Singular -q dump_$p.sing > cert_$p.log 2>&1 )
  echo "$(date +%T) p=$p $(grep -E 'guardrun\]' modp/cert_$p.log | sed 's/.*exit/exit/') $(grep -c '|' modp/cert_$p.txt 2>/dev/null) terms"
done
