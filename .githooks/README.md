# .githooks

In-repo git hooks. `pre-commit` is a **build gate**: any commit touching `*.lean`,
`lakefile.*`, `lake-manifest.json`, or `lean-toolchain` must `lake build` clean.

`core.hooksPath` is **local git config, not tracked** — re-run this on every fresh clone:

```sh
git config core.hooksPath .githooks
```

The gate is build-only (no protected-branch guard): `main` is this repo's working branch.
CI (`.github/workflows/ci.yml`) is the real pre-merge enforcement; this is the local reminder.
