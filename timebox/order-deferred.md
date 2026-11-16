# Timeboxed proof attempts (P0 order core)

Commands are run from the worktree root with the pinned `wiz`:

```
WIZ_LIGHT_SECS=180 /workspace/wiz-tools/light wiz check -I src <file>
```

## `R.nonneg_add`: resolved

The first attempt hung >180 s. The cause was a proof-direction error in the final
`Q.le_congr` (`Q.symm e2` was needed: `hsum` is at `-(1/m+1/n)`, the target at
`-1/m`). With the direction fixed, `R.nonneg_add` is in `src/Reals/RealOrder.wiz`
and the module checks. No language/tooling bug.

## `R.add_le_add`: deferred

The direct index proof needs the `(x'+y')-(x+y)` sequence at one index. Because
`R.Le x y` is `R.NonNeg (y-x)`, the index telescopes (`addIdx (nonnegIdx n)` inside
another `addIdx`), and the equality between `(x'+y'-(x+y)).seq s` and the explicit
difference is an OTT equality of the `Q` structure (a Σ), not a `Q.Eq`. A direct
`Q.ofEq (R.sub_seq …)` has to transport that Σ and did not finish in 180 s.
`R.le_antisymm` hits the same conversion when it assembles the three-term bound.
Neither is in `RealOrder.wiz`; `R.le_trans`, `R.nonneg_add`, `R.nonneg_congr`,
`R.nonneg_seq` are.

Exact check that was used (module compiles without the last two lemmas):

```
WIZ_LIGHT_SECS=180 /workspace/wiz-tools/light wiz check -I src src/Reals/RealOrder.wiz
```
