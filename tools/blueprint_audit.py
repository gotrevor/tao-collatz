#!/usr/bin/env -S uv run --quiet python3
r"""Blueprint audit — the node ledger is DERIVED, never hand-maintained.

The disease this cures: tao-collatz had FOUR hand-maintained status ledgers
(BLUEPRINT.md §2, blueprint/src/content.tex's \leanok flags, EXECUTABILITY.md's
"Live judge state", STATUS.md's axiom table). They drift independently, and a stale
ledger is worse than none — it launders a worker claim into a reviewer-facing fact.

The cure: ONE registry, everything else derived.

  blueprint/src/content.tex  is the registry.  It already carries, per node:
      \label{NODE}      the node id
      \lean{a, b, c}    the Lean declarations that node claims
      \leanok           (in the env)   the STATEMENT is formalized
      \leanok           (in a proof)   the PROOF is complete

  This tool reads that registry, asks the KERNEL what is actually true, and rules.

Four findings, in descending severity:

  FALSE-GREEN  a node's proof is marked \leanok but a declaration it claims is NOT
               axiom-clean (carries sorryAx, or an extra axiom). This is the one that
               lies to a reviewer. Exit code 1.
  DRIFT        a node names a declaration that does not exist in the Lean source.
  SEAM         a node claims NO theorem at all — only defs, or nothing. It contributes
               ZERO sorries while being unfinished, so the sorry census silently
               understates the distance to done. (Found independently by a Codex
               inventory pass, 2026-07-14; mechanized here so it cannot be forgotten.)
  MISSED-FLIP  every declaration is axiom-clean but the proof is not marked \leanok.
               The blueprint is understating real progress. (Judge pass 27 had to flip
               X4/X7/X8/X11 by hand — this is that, automated.)

Usage:
    tools/blueprint_audit.py                 # audit, print the report, gate on FALSE-GREEN
    tools/blueprint_audit.py --ledger        # also emit the generated markdown ledger
    tools/blueprint_audit.py --write-ledger  # write it to blueprint/LEDGER.md

The trust base is exactly [propext, Classical.choice, Quot.sound]. Anything else is a
finding, not a footnote.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TEX = REPO / "blueprint" / "src" / "content.tex"
SRC = REPO / "TaoCollatz"
TRUST_BASE = {"propext", "Classical.choice", "Quot.sound"}

THM_KINDS = ("theorem", "lemma", "example")
DEF_KINDS = ("def", "abbrev", "structure", "inductive", "instance", "noncomputable def")


# Environments that carry a proof obligation. A `definition` node with only defs is
# CORRECT, not a seam — the seam finding must not cry wolf on every definition block.
PROOF_ENVS = {"theorem", "lemma", "proposition", "corollary"}


@dataclass
class Node:
    label: str
    env: str = ""                                            # theorem | definition | ...
    decls: list[str] = field(default_factory=list)
    uses: list[str] = field(default_factory=list)            # \uses{} dependency edges
    stmt_ok: bool = False
    proof_ok: bool = False
    # filled by the audit
    kinds: dict[str, str] = field(default_factory=dict)     # decl -> thm | def | MISSING
    axioms: dict[str, set[str]] = field(default_factory=dict)  # decl -> axiom set

    @property
    def wants_proof(self) -> bool:
        return self.env in PROOF_ENVS

    @property
    def theorems(self) -> list[str]:
        return [d for d in self.decls if self.kinds.get(d) == "thm"]

    @property
    def missing(self) -> list[str]:
        return [d for d in self.decls if self.kinds.get(d) == "MISSING"]

    @property
    def unclean(self) -> list[str]:
        return [d for d in self.theorems if not self.axioms.get(d, set()) <= TRUST_BASE]

    @property
    def is_seam(self) -> bool:
        """A node that OWES a proof but names no theorem: zero sorries, still unfinished.

        The sorry census counts only holes someone has written down. A proposition with
        no Lean theorem behind it contributes nothing to that count and is not done.
        """
        return self.wants_proof and not self.theorems

    @property
    def false_stmt_green(self) -> bool:
        r"""A node that OWES a proof, names NO theorem, yet carries a statement `\leanok`.

        `\leanok` outside a proof block means "this STATEMENT is formalized in Lean". A seam
        that also claims it is asserting that a statement exists which does not. It renders
        green in the blueprint web while the theorem is simply absent — a false green one
        level up from the one the proof gate catches, and invisible to the sorry census.

        Found 2026-07-14 on C7: `\lean{passes, passTime, passLoc}` (three DEFS) + `\leanok`,
        on a `lemma` node whose real content is the estimate (1.19), which was nowhere in Lean.
        """
        return self.is_seam and self.stmt_ok

    @property
    def all_clean(self) -> bool:
        return bool(self.theorems) and not self.unclean and not self.missing


def parse_registry() -> list[Node]:
    r"""Read content.tex: env type, \label, \lean, and \leanok (statement vs proof)."""
    tex = TEX.read_text()
    nodes: list[Node] = []
    cur: Node | None = None
    in_proof = False
    pending_env = ""

    for line in tex.splitlines():
        # Strip TeX comments FIRST. Without this, a line of PROSE mentioning \leanok flips
        # the node green — a comment can silently ratify a node it is only talking about.
        # (Found 2026-07-14 the honest way: a comment added to document C7's false green
        # re-greened C7. An instrument that its own documentation can corrupt is not one.)
        line = re.sub(r"(?<!\\)%.*$", "", line)
        if not line.strip():
            continue
        if m := re.search(r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}", line):
            pending_env = m.group(1)
        if re.search(r"\\begin\{proof\}", line):
            in_proof = True
        if re.search(r"\\end\{proof\}", line):
            in_proof = False
        if m := re.search(r"\\label\{([^}]+)\}", line):
            lab = m.group(1)
            if lab.startswith("chp:") or lab.startswith("sec:"):
                continue                      # chapter/section anchors are not nodes
            cur = Node(label=lab, env=pending_env)
            nodes.append(cur)
            pending_env = ""
            in_proof = False
        if cur is None:
            continue
        if m := re.search(r"\\lean\{([^}]*)\}", line):
            cur.decls += [d.strip() for d in m.group(1).split(",") if d.strip()]
        if m := re.search(r"\\uses\{([^}]*)\}", line):
            # Statement-\uses and proof-\uses are unioned: either way the node cannot be
            # FINISHED until that dependency exists. Blocking order is what we need here.
            cur.uses += [d.strip() for d in m.group(1).split(",") if d.strip()]
        if re.search(r"\\leanok", line):
            if in_proof:
                cur.proof_ok = True
            else:
                cur.stmt_ok = True
    return nodes


def classify_kinds(nodes: list[Node]) -> None:
    """theorem/lemma vs def/abbrev/… — from the Lean source.

    Namespace-aware: a blueprint may name `PMF.cexpect` while the source declares
    `def cexpect` inside `namespace PMF`. Match the FULL dotted name or its final
    component; existence itself is settled by the kernel (below), not by this grep.
    """
    blob = "\n".join(p.read_text() for p in SRC.rglob("*.lean"))
    thm_kw = "|".join(THM_KINDS)
    def_kw = "|".join(k.split()[-1] for k in DEF_KINDS)
    for n in nodes:
        for d in n.decls:
            for cand in (d, d.split(".")[-1]):          # full name, then bare name
                esc = re.escape(cand)
                pre = r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                if re.search(rf"{pre}(?:{thm_kw})\s+{esc}\b", blob, re.M):
                    n.kinds[d] = "thm"
                    break
                if re.search(rf"{pre}(?:{def_kw})\s+{esc}\b", blob, re.M):
                    n.kinds[d] = "def"
                    break
            else:
                n.kinds[d] = "MISSING"


def run_axiom_check(nodes: list[Node]) -> None:
    """Ask the kernel. This is the ONLY thing that establishes proof status.

    Every declaration is probed (defs too) — that is what settles existence, so the
    DRIFT finding is the kernel's verdict rather than a grep's.
    """
    all_decls = sorted({d for n in nodes for d in n.decls})
    if not all_decls:
        return
    body = "import TaoCollatz\nopen TaoCollatz\n" + "".join(f"#print axioms {d}\n" for d in all_decls)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(body)
        scratch = f.name

    print(f"🔬 asking the kernel about {len(all_decls)} declarations (lake env lean)…", file=sys.stderr)
    proc = subprocess.run(["lake", "env", "lean", scratch], cwd=REPO,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr

    found: dict[str, set[str]] = {}
    for line in out.splitlines():
        if m := re.match(r"'([\w.'!]+)' depends on axioms: \[([^\]]*)\]", line):
            found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        elif m := re.match(r"'([\w.'!]+)' does not depend on any axioms", line):
            found[m.group(1)] = set()

    def lookup(d: str) -> set[str] | None:
        for key in (d, f"TaoCollatz.{d}"):                  # `open TaoCollatz` resolution
            if key in found:
                return found[key]
        for k, v in found.items():                          # last resort: suffix match
            if k.split(".")[-1] == d.split(".")[-1]:
                return v
        return None

    for n in nodes:
        for d in n.decls:
            ax = lookup(d)
            if ax is None:
                n.kinds[d] = "MISSING"       # the kernel cannot resolve it: real drift
            elif n.kinds.get(d) == "thm":
                n.axioms[d] = ax


def report(nodes: list[Node]) -> int:
    false_green, drift, seams, missed, false_stmt = [], [], [], [], []

    for n in nodes:
        if n.proof_ok and (n.unclean or n.missing):
            false_green.append(n)
        if n.missing:
            drift.append(n)
        if n.is_seam:
            seams.append(n)
        if n.false_stmt_green:
            false_stmt.append(n)
        # A `definition` node needs no proof block — its statement \leanok is the whole
        # story, even when it bundles a proved lemma. Only a proof-owing env can MISS a flip.
        if n.wants_proof and n.all_clean and not n.proof_ok:
            missed.append(n)

    print()
    if false_green:
        print("🚨 FALSE GREEN — proof marked \\leanok but the kernel disagrees:")
        for n in false_green:
            for d in n.unclean:
                extra = sorted(n.axioms[d] - TRUST_BASE)
                print(f"   {n.label:<5} {d}  ← {'sorryAx' if 'sorryAx' in extra else ','.join(extra)}")
            for d in n.missing:
                print(f"   {n.label:<5} {d}  ← declaration does not exist")
        print()

    if false_stmt:
        print("🚨 FALSE STATEMENT-GREEN — statement marked \\leanok, but NO theorem exists:")
        print("     the node renders GREEN in the blueprint web while its content is absent.")
        print("     A reader trusts the border and routes around the node. Drop the \\leanok")
        print("     (or \\notready it) until the statement is really in Lean.")
        for n in false_stmt:
            what = ", ".join(f"{d} ({n.kinds[d]})" for d in n.decls) or "nothing"
            print(f"   {n.label:<5} \\lean{{{what}}} — all defs, no theorem")
        print()

    if drift:
        print("⚠️  DRIFT — blueprint names declarations the Lean source does not have:")
        for n in drift:
            print(f"   {n.label:<5} {', '.join(n.missing)}")
        print()

    if seams:
        by_label = {n.label: n for n in nodes}
        seam_labels = {n.label for n in seams}
        done = lambda lab: (m := by_label.get(lab)) is not None and not m.is_seam  # noqa: E731

        print("🕳️  SEAMS — nodes claiming NO theorem (zero sorries, still unfinished):")
        print("     the sorry census cannot see these. This is the distance-to-done gap.")
        for n in seams:
            what = ", ".join(f"{d} ({n.kinds[d]})" for d in n.decls) or "— nothing claimed —"
            print(f"   {n.label:<5} {what}")
            # A FLAT seam list invites the reader to treat seams as independent. They are not:
            # a seam upstream of another seam must be PROVED before the downstream one can be
            # CLOSED (its statement can still be pinned first — statement-deps ≠ proof-deps).
            # Cost the judge a wrong campaign order once (pass 29); the list now carries it.
            blocks = sorted(m.label for m in nodes if n.label in m.uses)
            unmet = sorted(u for u in n.uses if u in seam_labels or not done(u))
            bits = []
            if blocks:
                bits.append(f"blocks {', '.join(blocks)}")
            if not unmet:
                bits.append("✅ deps met — ATTACKABLE NOW")
            else:
                # STATEMENT-deps ≠ PROOF-deps, and the difference decides the campaign order.
                # If every declaration of the unmet dep EXISTS (its defs are in Lean, only its
                # theorem is missing), this node's STATEMENT can be pinned today — only its
                # PROOF is blocked. That is what lets you de-risk a scary downstream node
                # (pin + route + probe) BEFORE grinding out a cheap upstream one, which is the
                # standing charter's breadth-first rule. Say so, or a reader reads "⛔" as
                # "do not touch" and de-risks in the wrong order.
                defs_exist = all(
                    by_label[u].decls and not by_label[u].missing
                    for u in unmet if u in by_label
                )
                if defs_exist:
                    bits.append(f"⛔ PROOF needs {', '.join(unmet)} · "
                                f"📌 statement PINNABLE NOW (their defs exist)")
                else:
                    bits.append(f"⛔ needs {', '.join(unmet)} first")
            print(f"   {'':<5} └─ {' · '.join(bits)}")
        print()

    if missed:
        print("🟢 MISSED FLIP — every declaration is axiom-clean, proof not marked \\leanok:")
        for n in missed:
            print(f"   {n.label:<5} {', '.join(n.theorems)}")
        print("     (the blueprint is UNDERSTATING real progress — flip these)")
        print()

    proved = [n for n in nodes if n.proof_ok and n.all_clean]
    print(f"📊 {len(proved)} nodes proved + axiom-clean · {len(seams)} seams · "
          f"{len(drift)} drift · {len(false_green) + len(false_stmt)} false-green "
          f"({len(false_green)} proof, {len(false_stmt)} statement)")

    if false_green or false_stmt:
        print("\n❌ GATE FAILED — a reviewer-facing \\leanok is not backed by the kernel.")
        return 1
    print("\n✅ no false greens: every \\leanok is kernel-backed, statement and proof.")
    return 0


def ledger(nodes: list[Node]) -> str:
    rows = ["| node | status | declarations |", "|---|---|---|"]
    for n in nodes:
        if n.is_seam:
            status = "🕳️ **seam** (no theorem — zero sorries, unfinished)"
        elif n.unclean:
            status = ("🟡 open (`sorryAx`)"
                      if any("sorryAx" in n.axioms.get(d, set()) for d in n.unclean)
                      else "🔴 extra axiom")
        elif n.missing:
            status = "⚠️ drift"
        elif not n.wants_proof:
            # a definition node: nothing to prove. Say so, rather than leaving a blank
            # that reads like an omission.
            status = "📐 definitions" + (" + lemma, axiom-clean" if n.all_clean else "")
        elif n.all_clean and n.proof_ok:
            status = "🟢 **proved, axiom-clean**"
        elif n.all_clean:
            status = "🟢 clean (flip pending)"
        else:
            status = "—"
        rows.append(f"| `{n.label}` | {status} | {', '.join(f'`{d}`' for d in n.decls) or '—'} |")
    return "\n".join(rows)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", action="store_true", help="print the generated ledger")
    ap.add_argument("--write-ledger", action="store_true", help="write blueprint/LEDGER.md")
    args = ap.parse_args()

    nodes = parse_registry()
    classify_kinds(nodes)
    run_axiom_check(nodes)
    rc = report(nodes)

    if args.ledger or args.write_ledger:
        table = ledger(nodes)
        header = (
            "# Node ledger — GENERATED, do not hand-edit 🤖\n\n"
            "Produced by `tools/blueprint_audit.py` from `blueprint/src/content.tex` (the node\n"
            "registry) + a live `#print axioms` run. **Proof status exists only via the kernel.**\n"
            "A hand-maintained ledger launders a worker claim into a reviewer-facing fact; this\n"
            "one cannot, because nothing in it is typed by hand.\n\n"
            "Trust base = `[propext, Classical.choice, Quot.sound]`.\n\n"
        )
        if args.write_ledger:
            (REPO / "blueprint" / "LEDGER.md").write_text(header + table + "\n")
            print("\n📝 wrote blueprint/LEDGER.md")
        else:
            print("\n" + header + table)
    return rc


if __name__ == "__main__":
    sys.exit(main())
