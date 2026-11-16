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
| `Reals.Nat` | the commutative semiring laws of `Nat`, its order (`Nat.Le` from the Prelude's Boolean `Nat.le`) |
| `Reals.Ring` | `nat_ring!`: a reflective normaliser for commutative semirings, with its soundness proof |
| `Reals.Int`, `Reals.IntRing` | the ring laws of `Int` through pairs of naturals; `int_pair_ring!` |
| `Reals.ZRing` | `int_ring!`: normalisation with integer coefficients |
| `Reals.IntOrder` | the order of `Int`, `Int.abs` |
| `Reals.Rat`, `Reals.QRing`, `Reals.QLaws` | `Q` (unreduced fractions, a setoid), `q_ring!`; ordered field: ring laws, congruences, order, `abs`, triangle inequality, inverse (`p * Q.inv p ≈ 1`), the archimedean property |
| `Reals.QSeq` | `1/(n+1)` (decreasing: `Q.invS_le_add`), and "below `b + k/(m+1)` for all `m` means below `b`" |
| `Reals.Real` | `R` (regular sequences), `≈` (an equivalence, by Bishop's criterion `R.eq_of_bound`), `+`, `-`, the additive group laws |
| `Reals.RealMul` | `·` (Bishop's, through a bound of the factors), commutativity, associativity, `1`, distributivity, congruence |
| `Reals.RealOrder` | positivity (a rational lower bound with a tail bound, as data), non-negativity at the shifted index `3n+2` (`R.NonNeg`), `R.le_refl`/`R.le_trans`, closure of `NonNeg` under `+` and `≈`, every real is below a natural number (`R.archimedean`), `|x|` |
| `Reals.Complete` | distances; **completeness**: a regular sequence of reals converges to `R.lim` (`R.lim_spec`); continuity of `+` and `·` with explicit moduli (`R.add_dist`, `R.mul_dist`) |
| `Reals.Analysis` | distance algebra (`R.dist_symm`, `R.dist_triangle`, `R.dist_neg`, `R.dist_of_forall_add`), limits (`R.lim_congr`, `R.lim_unique`, `R.lim_dist`), shrinking nested intervals (`R.Nested`, `R.Nested.lo_dist`/`hi_dist`), and the bisection root theorem: a continuous `f` with a sign-certified `R.Bracket` has `R.Dist (f (R.Nested.lim …)) 0 0` (`R.ivt_approx`) |
| `Reals.Isqrt`, `Reals.Sqrt2` | integer square root with its specification, the iff characterisation `Nat.isqrt_eq_iff`, `le_isqrt`, `isqrt_lt`, `sqrt_add_eq`, and uniqueness (`Nat.isqrt_unique`); `√2` as a real with `R.sqrt2_sq : R.sqrt2 * R.sqrt2 ≈ 2`; digits `d/P` with `|(d/P)² - 2| ≤ 4/P` (`Sqrt2.approx_sq`) |

Not done (see FINDINGS.md, "What is missing"): the rest of the real order core
(`add_le_add`, `le_antisymm`, `mul_le_mul`, `abs_triangle`, `le_of_forall_pos`,
`lt_cotrans`), the inverse of a real apart from zero, and the part of the intermediate
value theorem that *constructs* the bisection certificate from `f(a) < 0 < f(b)`.
`R.ivt_approx` proves the limit/root step; the certificate needs a located sign test,
the constructive boundary discussed in DESIGN.md. `timebox/order-deferred.md` records
the two order attempts that were stopped.

## Building

`wiz-toolchain` names the Wiz commit this is developed against (master `50cd3e7`; it
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
