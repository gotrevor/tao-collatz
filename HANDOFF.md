# HANDOFF — big-C campaign, lap 0 (host-staged)

**You are lap 1 of the big-C campaign.** Read `DIRECTION.md` first — it outranks this file.

State at handoff:
- Branch `explicit-big-c` off `origin/main` (= PR #9 squash: `cTao` + the explicit-exponent
  theorem, merged and ratified).
- The pin is planted in BOTH surfaces (`TaoCollatz/Statement.lean` sorry + comparator
  challenge/config) — judge-owned, you write only the proof side.
- `tools/tao_stmt_diff.py` hardened this commit: def VALUES now pinned (`cTao`, `CTao`),
  challenge file in scope. Run it per commit against the setup commit or later.
- `lean-sorry -c TaoCollatz` = 1 (the pin — by design, under a local
  `set_option warningAsError false in` shield so `lake build` stays green everywhere;
  the red-until-done finish line is the `comparator` CI check).

Start with DIRECTION step 1 (the check17 map). Do not start step 2 until the map names
every node with file:line.
