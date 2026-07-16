# Judge seat — start here 🪷⚖️

## 1. Read `judge/JUDGE.md` — the standing brief (durable: rules, instruments, lessons).
## 2. Then the newest timestamped handoff below — the live state (what changed, what to hunt).

**The live handoff is the newest `judge/HANDOFF-JUDGE-<YYYY-MM-DD-HHMM>.md`.**

```bash
ls -t judge/HANDOFF-JUDGE-*.md | head -1     # <- read that
```

Judge handoffs are **timestamped per pass** (Trevor, 2026-07-14), the same convention the lap
handoffs use — so the seat has a history instead of a single file overwritten into amnesia, and
so a fresh session can see at a glance how stale its briefing is.

Two things this file exists to tell you:

1. ⏱️ **Judge handoff timestamps are REAL local time.** The *lap* handoffs
   (`HANDOFF-2026-07-15-*.md`, repo root) run on a **drifted clock** and are named up to a day
   ahead of wall-clock. Never order judge passes against lap-handoff filenames.
2. 📌 **This pointer stays put.** New pass ⟹ write a new timestamped handoff; leave this file
   alone. It is the stable entry point ("read `judge/HANDOFF-JUDGE.md` and take it from there"),
   and the durable content lives in the protocol docs it points at, not here:

   - `EXECUTABILITY.md` → "Judge loop — standing ops" (the per-pass recipe), "Live judge state",
     "Campaign log" (index of `judge/pass-NN.md`)
   - `DIRECTION.md` → CURRENT DIRECTIVE (the judge writes it; it outranks every handoff)
   - `BLUEPRINT.md` → durable design · `blueprint/LEDGER.md` → **generated** node status
