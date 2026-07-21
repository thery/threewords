#!/usr/bin/env python3
"""Regenerate the paper3 -> code link table in README.md.

Each row of CODE_MAP names a paper3 object (algorithm / theorem / definition)
and the Rocq identifier + file that formalises it.  This script finds the
current line of every identifier and rewrites the table (with GitHub blob
links) between the CODE-LINKS markers in README.md, so the links stay correct
when the sources move.  Run it after editing the Coq sources:

    python3 scripts/gen_code_links.py            # rewrite README.md
    python3 scripts/gen_code_links.py --check     # exit 1 if out of date

Wire it into a git pre-commit hook to update automatically (see README).
"""

import re
import sys
import pathlib

REPO = "thery/threewords"
BRANCH = "main"
COQ_DIR = "code/coq"

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
START = "<!-- CODE-LINKS:START -->"
END = "<!-- CODE-LINKS:END -->"

# (paper object, Rocq identifier, file).  Identifier is matched at the start of
# a line after one of Lemma/Theorem/Definition/Fixpoint/Corollary/Record.
CODE_MAP = [
    ("Def. 1 — P-nonoverlapping",   "Pnonoverlap",              "Nonoverlap.v"),
    ("Def. 2 — F-nonoverlapping",   "Fnonoverlap_aux",          "Nonoverlap.v"),
    ("Def. 3 — nonoverlap (wIZ)",   "Fnonoverlap",              "Nonoverlap.v"),
    ("Def. 5 — triple word",        "isTW",                     "TWR.v"),
    ("Alg. 1 — Fast2Sum",           "Fast2Sum_correct_aux",     "Fast2Sum_robust_flx.v"),
    ("Alg. 2 — 2Sum",               "TwoSum",                   "TwoSum.v"),
    ("Alg. 2 — 2Sum correctness",   "TwoSum_correct_loc",       "TwoSum.v"),
    ("Alg. 4 — VecSum",             "vecSum",                   "VecSum.v"),
    ("Thm. 1 — VecSum F-nonoverlap","vecSum_Fnonoverlap_core",  "VecSum.v"),
    ("Cor. 1 — VecSum (overlap)",   "vecSum_Fnonoverlap",       "VecSum.v"),
    ("Cor. 1 — bump reduction",     "Cor1_bump_Thm1_hyp",       "VecSum.v"),
    ("Alg. 5 — VSEB",               "vseb",                     "VSEB.v"),
    ("Thm. 2 — VSEB P-nonoverlap",  "vseb_Pnonoverlap",         "VSEB.v"),
    ("Thm. 3 — truncation error",   "Pnonoverlap_truncate_error","Nonoverlap.v"),
    ("Alg. 6 — ToTW",               "ToTW",                     "TWSum.v"),
    ("Thm. 4 — ToTW is a TW",       "ToTW_isTW",                "TWSum.v"),
    ("Alg. 8 — TWSum",              "TWSum",                    "TWSum.v"),
    ("Thm. 6 — VSEB(VecSum) P-nonov","vecSum_vseb_Pnonoverlap", "Thm6.v"),
    ("Thm. 6 — TWSum is a TW",      "TWSum_isTW",               "addition.v"),
    ("error bound — 2u³+4.2u⁴","TWSum_error",         "addition.v"),
]

KINDS = "Lemma|Theorem|Definition|Fixpoint|Corollary|Record|Inductive|Fact"


def find_line(path, ident):
    pat = re.compile(r"^(?:%s)\s+%s\b" % (KINDS, re.escape(ident)))
    for i, line in enumerate(path.read_text().splitlines(), 1):
        if pat.match(line):
            return i
    return None


def build_table():
    rows = ["| paper3 | Rocq | file |", "|--------|------|------|"]
    missing = []
    for obj, ident, fname in CODE_MAP:
        path = ROOT / COQ_DIR / fname
        line = find_line(path, ident) if path.exists() else None
        if line is None:
            missing.append("%s (%s in %s)" % (obj, ident, fname))
            rows.append("| %s | `%s` | **NOT FOUND** |" % (obj, ident))
            continue
        url = "https://github.com/%s/blob/%s/%s/%s#L%d" % (
            REPO, BRANCH, COQ_DIR, fname, line)
        rows.append("| %s | [`%s`](%s) | `%s:%d` |" % (
            obj, ident, url, fname, line))
    return "\n".join(rows), missing


def splice(text, table):
    block = "%s\n\n%s\n\n%s" % (START, table, END)
    if START in text and END in text:
        return re.sub(re.escape(START) + r".*?" + re.escape(END),
                      block.replace("\\", "\\\\"), text, flags=re.S)
    # append a section if the markers are absent
    return text.rstrip() + "\n\n## Code links\n\n" + block + "\n"


def main():
    check = "--check" in sys.argv[1:]
    table, missing = build_table()
    for m in missing:
        print("WARNING: identifier not found: %s" % m, file=sys.stderr)
    text = README.read_text()
    new = splice(text, table)
    if check:
        if new != text:
            print("README.md code links are out of date; run "
                  "scripts/gen_code_links.py", file=sys.stderr)
            sys.exit(1)
        print("README.md code links up to date.")
        return
    if new != text:
        README.write_text(new)
        print("Updated %d links in README.md." % len(CODE_MAP))
    else:
        print("README.md already up to date.")
    if missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
