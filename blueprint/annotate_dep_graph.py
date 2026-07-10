#!/usr/bin/env python3
"""Surface per-node campaign estimates (laps + risk) on the dependency graph.

Post-processes web/dep_graph_document.html after `leanblueprint web`:
  * node fill tint by risk  — pale red (high) / amber (medium) / green (low);
    applied ONLY to nodes with no status fill of their own, so leanblueprint's
    proof-status backgrounds (blue = ready, green = proved) always win — a node
    that has progressed past "unstarted" keeps its status color and shows the
    estimate via label + tooltip only;
  * second label line       — the estimated treadmill-lap range;
  * hover tooltip           — laps + risk word + confidence;
  * legend entries for the three tints.

Single source of truth: the \\lapsrisk{laps}{risk}{conf} annotations in
src/content.tex (which mirror BLUEPRINT.md §2's ledger). Rerun after every
`leanblueprint web` — use ./build.sh, which chains the two. Idempotent.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = HERE / "src/content.tex"
HTML = HERE / "web/dep_graph_document.html"

TINT = {"high": "#FFE2E0", "medium": "#FFF6DA", "low": "#E9F6EC"}

ENV_RE = re.compile(r"\\label\{([A-Z]\d+)\}(.*?)\\end\{", re.DOTALL)
LAPSRISK_RE = re.compile(r"\\lapsrisk\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}")
NODE_RE = re.compile(r"(?P<pre>[;{]\s*)(?P<id>[A-Z]\d+)\s*\[(?P<attrs>[^\]]*)\]")


def read_estimates() -> dict[str, tuple[str, str, str]]:
    """label -> (laps '8–15', risk word, conf '90%'), from content.tex."""
    out = {}
    for m in ENV_RE.finditer(TEX.read_text()):
        label, body = m.group(1), m.group(2)
        lr = LAPSRISK_RE.search(body)
        if not lr:
            continue
        laps = lr.group(1).replace("--", "–")
        risk_full = lr.group(2)
        risk_word = risk_full.split()[0]  # "high --- risk kernel 1" -> "high"
        conf = lr.group(3).replace("\\%", "%")
        out[label] = (laps, risk_word, conf)
    return out


def patch_node(m: re.Match, est: dict) -> str:
    node_id, attrs = m.group("id"), m.group("attrs")
    if node_id not in est or "tooltip=" in attrs:
        return m.group(0)
    laps, risk, conf = est[node_id]
    # Two-line label: id + lap range. The file holds \\n so the JS template
    # literal collapses it to \n, which graphviz renders as a line break.
    attrs = re.sub(rf"label={node_id}\b", f'label="{node_id}\\\\n{laps}"', attrs)
    attrs += f',\t\ttooltip="{laps} laps · risk {risk} · {conf} confidence"'
    if "fillcolor" not in attrs:  # never override a leanblueprint status fill
        attrs += f',\t\tstyle=filled,\t\tfillcolor="{TINT[risk]}"'
    return f"{m.group('pre')}{node_id}\t[{attrs}]"


LEGEND_ANCHOR = "<dt>Dark green border</dt><dd>this is in Mathlib</dd>"
LEGEND_EXTRA = (
    "\n      \n      <dt>Pale red background</dt><dd>campaign risk: <em>high</em> "
    "(unstarted node; label's second line = estimated treadmill laps)</dd>"
    "\n      \n      <dt>Pale amber background</dt><dd>campaign risk: <em>medium</em></dd>"
    "\n      \n      <dt>Pale green background</dt><dd>campaign risk: <em>low</em></dd>"
)


def main() -> int:
    est = read_estimates()
    if not est:
        sys.exit("no \\lapsrisk annotations found in content.tex")
    html = HTML.read_text()
    patched, n = NODE_RE.subn(lambda m: patch_node(m, est), html)
    if LEGEND_ANCHOR in patched and "campaign risk" not in patched:
        patched = patched.replace(LEGEND_ANCHOR, LEGEND_ANCHOR + LEGEND_EXTRA, 1)
    HTML.write_text(patched)
    annotated = sum(1 for i in est if f'tooltip="{est[i][0]}' in patched)
    print(f"dep graph: {len(est)} estimates in tex, {n} node attrs scanned, "
          f"{annotated} nodes annotated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
