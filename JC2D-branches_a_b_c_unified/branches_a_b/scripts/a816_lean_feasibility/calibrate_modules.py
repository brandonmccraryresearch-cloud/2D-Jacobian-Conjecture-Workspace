"""calibrate_modules.py -- monomial-product counts of reflective certificate modules (Lean `Expr` syntax of
BranchAb.ChartProof.Reflect), for calibrating kernel time per product.

For each module it finds the `lc_zero` / `lc_zero2` invocations, parses every reflected expression (the target and
each (cofactor, fact) pair; named facts are looked up in the given definition files), normalizes them with
python-flint over Z, and reports: products = sum over pairs of |cofactor| * |fact| (normalized term counts), the
target size, and the maximal numeral size in digits.
usage: python3 calibrate_modules.py DEFS.lean[,DEFS2.lean] MODULE.lean [MODULE2.lean ...]
"""
import sys, re, threading
import flint

sys.setrecursionlimit(1000000)
threading.stack_size(1 << 29)
sys.set_int_max_str_digits(0)

NV = 80
CTX = flint.fmpz_mpoly_ctx.get(tuple(f"v{i}" for i in range(NV)), "lex")
GENS = CTX.gens()
TOK = re.compile(r"\(|\)|\.[a-zA-Z]+|-?\d+|[A-Za-z_][A-Za-z_0-9']*|,|\[|\]|⟨|⟩")


class Parser:
    def __init__(self, text, named):
        self.t = TOK.findall(text)
        self.i = 0
        self.named = named
        self.maxdig = 0

    def peek(self):
        return self.t[self.i]

    def take(self):
        tok = self.t[self.i]; self.i += 1; return tok

    def expr(self):
        tok = self.take()
        if tok == "(":
            head = self.peek()
            if head.startswith("."):
                self.take()
                if head == ".num":
                    n = self.intlit()
                    self.maxdig = max(self.maxdig, len(str(abs(n))))
                    val = CTX.from_dict({}) + n
                elif head == ".var":
                    val = GENS[int(self.take())]
                elif head == ".neg":
                    val = -self.expr()
                elif head in (".add", ".sub", ".mul"):
                    a = self.expr(); b = self.expr()
                    val = a + b if head == ".add" else (a - b if head == ".sub" else a * b)
                elif head == ".pow":
                    a = self.expr(); k = int(self.take())
                    val = a ** k
                else:
                    raise ValueError(head)
                assert self.take() == ")"
                return val
            # parenthesized expression or tuple handled by caller
            val = self.expr()
            assert self.take() == ")"
            return val
        if tok in self.named:
            return self.named[tok]
        raise ValueError(f"unexpected token {tok!r} at {self.i}")

    def intlit(self):
        tok = self.take()
        if tok == "(":
            n = int(self.take()); assert self.take() == ")"; return n
        return int(tok)


def defs_of(text, named):
    out = {}
    for m in re.finditer(r"noncomputable def (\w+) : Expr :=\s*\n\s*(.*)", text):
        name, body = m.group(1), m.group(2)
        p = Parser(body, {**named, **out})
        out[name] = p.expr()
    return out


def pairs_after(text, start, named):
    """parse `[((c), e), ((c), e), ...]` starting at text[start] == '['; returns list of (c, e) polys"""
    p = Parser(text[start:], named)
    assert p.take() == "["
    pairs = []
    if p.peek() == "]":
        p.take(); return pairs, p.maxdig
    while True:
        assert p.take() == "("            # tuple open
        c = p.expr()
        assert p.take() == ","
        e = p.expr()
        assert p.take() == ")"
        pairs.append((c, e))
        tok = p.take()
        if tok == "]":
            break
        assert tok == ",", tok
    return pairs, p.maxdig


def main():
    defs_files = sys.argv[1].split(",")
    named = {}
    for f in defs_files:
        named.update(defs_of(open(f).read(), named))
    for mod in sys.argv[2:]:
        text = open(mod).read()
        local = defs_of(text, named)
        allnamed = {**named, **local}
        tot_prod, npairs, maxdig = 0, 0, 0
        for m in re.finditer(r"lc_zero2? ctx (\w+) ", text):
            tgt = allnamed[m.group(1)]
            pos = m.end()
            lists = []
            for _ in range(2 if "lc_zero2" in m.group(0) else 1):
                while text[pos] != "[":
                    pos += 1
                # find the matching ']' by parsing
                pairs, md = pairs_after(text, pos, allnamed)
                maxdig = max(maxdig, md)
                lists.append(pairs)
                # advance pos past this list: count brackets
                depth = 0
                while True:
                    ch = text[pos]
                    if ch == "[":
                        depth += 1
                    elif ch == "]":
                        depth -= 1
                        if depth == 0:
                            pos += 1; break
                    pos += 1
            for pairs in lists:
                for c, e in pairs:
                    tot_prod += len(c.to_dict()) * len(e.to_dict()); npairs += 1
        tgt_terms = sum(len(v.to_dict()) for v in local.values())
        md_local = max((max((len(str(abs(int(c)))) for c in v.to_dict().values()), default=0)
                        for v in local.values()), default=0)
        print(f"{mod.split('/')[-1]}: pairs {npairs}, products {tot_prod}, local-def terms {tgt_terms}, "
              f"max digits {max(maxdig, md_local)}, source bytes {len(text)}")


t = threading.Thread(target=main)
t.start(); t.join()
