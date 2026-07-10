#!/usr/bin/env bash
# Rebuild the blueprint web AND re-apply the dep-graph campaign-estimate overlay.
# Always use this instead of a bare `leanblueprint web` — regeneration wipes the
# overlay (annotate_dep_graph.py re-derives it from content.tex's \lapsrisk lines).
set -euo pipefail
cd "$(dirname "$0")/.."
leanblueprint web
python3 blueprint/annotate_dep_graph.py
