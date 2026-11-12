# wiz-reals

The real numbers, constructed and reasoned about in [Wiz](https://github.com/badly-drawn-wizards/wiz),
a dependently typed language with observational type theory, and built with grail
(Wiz's build tool). Everything is checked by the Wiz kernel; nothing is assumed
(`#print axioms R.sqrt2_sq`, `R.lim_spec`, `R.mul_assoc`: "does not depend on any axioms").

It exists to find out how usable Wiz is for real mathematics, and to write down what
that was like: see [FINDINGS.md](FINDINGS.md). [DESIGN.md](DESIGN.md) says why the
reals are Bishop's regular sequences and how the algebra is automated.

## What is here

| module | contents |
|---|---|
| (lib, wiz #221) | `Nat`, `Order`, `Ring` (`nat_ring!`), `Int`, `IntRing` (`int_pair_ring!`, `int_ring!`), `IntOrder`, `Rat` (`Q`, unreduced fractions, a setoid; `q_ring!`; the ordered field), `RingTactic` (`by ring`, #227): these were this project's modules and are in Wiz's library now (branch `cleanup`) |
| `Reals.QSeq` | `1/(n+1)`, and "below `b + k/(m+1)` for all `m` means below `b`" |
| `Reals.Real` | `R` (regular sequences), `≈` (an equivalence, by Bishop's criterion `R.eq_of_bound`), `+`, `-`, the additive group laws |
| `Reals.RealMul` | `·` (Bishop's, through a bound of the factors), commutativity, associativity, `1`, distributivity, congruence |
| `Reals.RealOrder` | positivity (as data), non-negativity, every real is below a natural number (`R.archimedean`), `|x|` |
| `Reals.Complete` | distances; **completeness**: a regular sequence of reals converges to `R.lim` (`R.lim_spec`); continuity of `+` and `·` with explicit moduli (`R.add_dist`, `R.mul_dist`) |
| `Reals.Isqrt`, `Reals.Sqrt2` | integer square root with its specification; `√2` as a real with `R.sqrt2_sq : R.sqrt2 * R.sqrt2 ≈ 2`; digits `d/P` with `|(d/P)² - 2| ≤ 4/P` (`Sqrt2.approx_sq`) |

Not done (see FINDINGS.md, "What is missing"): the inverse of a real apart from zero,
the intermediate value theorem.

## Building

`wiz-toolchain` names the Wiz commit this is developed against (master `183f823`; it
has a release snapshot). With [tower](https://github.com/badly-drawn-wizards/wiz/blob/master/docs/stages/26-tower.md)
on `PATH`, `wiz` and `grail` in this directory use it (`tower show`); the release ships
its own C compiler and GMP.

```sh
grail build          # check every module (the kernel checks every proof) and compile .grail/bin/sqrt2
grail test           # tests/: digits computed by the kernel and by compiled code
.grail/bin/sqrt2     # √2 to 60 places, and the certified error bound
```

The first `grail build` takes about a minute and a half on one core; after that
grail's cache answers.

```
$ .grail/bin/sqrt2
sqrt 2 = 1.414213562373095048801688724209698078569671875376948073176679
d^2 <= 2*10^120 < (d+1)^2: true
proved (Sqrt2.approx_sq): |q^2 - 2| <= 4/10^60 for q = d/10^60
```

## Licence

GPL-3.0-or-later.
