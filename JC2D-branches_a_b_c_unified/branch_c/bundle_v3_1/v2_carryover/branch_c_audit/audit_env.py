"""audit_env.py -- locations used by the audit scripts in this directory.

Run every audit script from inside branch_c_audit/ (they read and write ./work/ and ./*.pkl).
  BRANCH_C_CERTGEN  the certgen/ directory of the branch-(a,b) Lean project (it holds gen_system.py and
                    e5_exact_K5.json), e.g. <repo>/branch_ab_v17/lean/certgen.  Needed by stage6e_audit*.py.
  SINGULAR          the Singular binary.  Default: `Singular` on PATH.
"""
import os
import shutil
import sys


def need_certgen():
    d = os.environ.get("BRANCH_C_CERTGEN", "")
    if not os.path.exists(os.path.join(d, "gen_system.py")):
        sys.exit("set BRANCH_C_CERTGEN to the certgen/ directory of the branch-(a,b) Lean project "
                 "(the one holding gen_system.py and e5_exact_K5.json)")
    return d


def need_singular():
    s = os.environ.get("SINGULAR") or shutil.which("Singular") or ""
    if not s or not os.path.exists(s):
        sys.exit("Singular not found: put it on PATH or set SINGULAR=/path/to/Singular")
    return s
