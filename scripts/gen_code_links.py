#!/usr/bin/env python3
"""Regenerate the paper3 coverage table (with code links) in README.md.

Each row of COVERAGE names a paper3 algorithm and its theorem(s), each carrying
the Rocq identifier + file that formalises it (or None when not formalised).
This script looks up the current line of every identifier and rewrites the
coverage table -- with GitHub blob links on the formalised entries -- between
the CODE-LINKS markers in README.md, so the links stay correct when the sources
move.  Run it after editing the Coq sources:

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

# A reference into the sources: (Rocq identifier, file) or None.
def R(ident, fname):
    return (ident, fname)

# Coverage rows: (alg label, object text, object ref, [ (thm label, ref) ... ],
#                 status).  status in {"done", "skel", "no"}.
# A ref is R(ident, file) when formalised, else None.
COVERAGE = [
    ("1",     "Fast2Sum",  None,
     [("correctness", R("Fast2Sum_correct_aux", "Fast2Sum_robust_flx.v"))],
     "done"),
    ("2",     "2Sum",      R("TwoSum", "TwoSum.v"),
     [("correctness", R("TwoSum_correct_loc", "TwoSum.v"))], "done"),
    ("3",     "2Prod (FMA)", None,
     [], "no"),
    ("4",     "VecSum",    R("vecSum", "VecSum.v"),
     [("Thm 1", R("vecSum_Fnonoverlap_core", "VecSum.v")),
      ("Cor 1", R("vecSum_Fnonoverlap", "VecSum.v"))], "done"),
    ("5",     "VSEB",      R("vseb", "VSEB.v"),
     [("Thm 2", R("vseb_Pnonoverlap", "VSEB.v"))], "done"),
    ("",      "keep-first-`k` error", None,
     [("Thm 3", R("Pnonoverlap_truncate_error", "Nonoverlap.v"))], "done"),
    ("6",     "ToTW",      R("ToTW", "TWSum.v"),
     [("Thm 4", R("ToTW_isTW", "TWSum.v"))], "skel"),
    ("7",     "RoundTW",   None,
     [("Thm 5", None)], "no"),
    ("8",     "TWSum",     R("TWSum", "TWSum.v"),
     [("Thm 6", R("vecSum_vseb_Pnonoverlap", "Thm6.v")),
      ("error", R("TWSum_error", "addition.v"))], "done"),
    ("9–10",  "3Prod (TW×TW)", None,
     [("Thm 7", None)], "no"),
    ("11–12", "3Prod (DW×TW)", None,
     [("Thm 8", None)], "no"),
    ("13",    "3Reci",     None,
     [("Thm 9", None)], "no"),
    ("14",    "3Div",      None,
     [("Thm 10", None)], "no"),
    ("15",    "3SqRt",     None,
     [("Thm 11", None)], "no"),
]

STATUS = {"done": "✅", "skel": "🚧", "no": "❌"}

KINDS = "Lemma|Theorem|Definition|Fixpoint|Corollary|Record|Inductive|Fact"


def find_line(path, ident):
    pat = re.compile(r"^(?:%s)\s+%s\b" % (KINDS, re.escape(ident)))
    for i, line in enumerate(path.read_text().splitlines(), 1):
        if pat.match(line):
            return i
    return None


def link(text, ref, missing):
    """Render text as a GitHub link if ref is a resolvable (ident, file)."""
    if ref is None:
        return text
    ident, fname = ref
    path = ROOT / COQ_DIR / fname
    line = find_line(path, ident) if path.exists() else None
    if line is None:
        missing.append("%s in %s" % (ident, fname))
        return "%s (**?**)" % text
    url = "https://github.com/%s/blob/%s/%s/%s#L%d" % (
        REPO, BRANCH, COQ_DIR, fname, line)
    return "[%s](%s)" % (text, url)


def build_table():
    missing = []
    rows = [
        "Links point at the Rocq definition/theorem. "
        "✅ proved · 🚧 skeleton (reduction proved, 1 admit) · ❌ not formalised.",
        "",
        "| Alg | Paper object | Theorem | Status |",
        "|----:|--------------|---------|:------:|",
    ]
    for alg, obj, obj_ref, thms, status in COVERAGE:
        objcell = link(obj, obj_ref, missing)
        if thms:
            thmcell = " + ".join(link(lbl, ref, missing) for lbl, ref in thms)
        else:
            thmcell = "—"
        rows.append("| %s | %s | %s | %s |" % (
            alg, objcell, thmcell, STATUS[status]))
    return "\n".join(rows), missing


def splice(text, table):
    block = "%s\n\n%s\n\n%s" % (START, table, END)
    if START in text and END in text:
        return re.sub(re.escape(START) + r".*?" + re.escape(END),
                      lambda _m: block, text, flags=re.S)
    return text.rstrip() + "\n\n## Coverage of paper3\n\n" + block + "\n"


def main():
    check = "--check" in sys.argv[1:]
    table, missing = build_table()
    for m in missing:
        print("WARNING: identifier not found: %s" % m, file=sys.stderr)
    text = README.read_text()
    new = splice(text, table)
    if check:
        if new != text:
            print("README.md coverage table is out of date; run "
                  "scripts/gen_code_links.py", file=sys.stderr)
            sys.exit(1)
        print("README.md coverage table up to date.")
        return
    if new != text:
        README.write_text(new)
        print("Updated coverage table (%d rows) in README.md." % len(COVERAGE))
    else:
        print("README.md already up to date.")
    if missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
