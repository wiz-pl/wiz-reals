# Design

## What Wiz offers, and what it doesn't

Wiz's kernel is observational type theory (Pujet and Tabareau) with a strict,
proof-irrelevant, impredicative `Prop`:

* **function extensionality and propositional extensionality are definitional**
  (`f = g` *is* `(x : A) → f x = g x`; `P = Q` *is* `P ↔ Q`);
* **proofs are irrelevant**: any two proofs of a proposition are convertible, so a
  structure with a proof field (`Q.pos`) needs nothing extra for its equality;
* there are **no quotient types**, no choice, and **no inductive propositions**:
  `∨` and `∃` are Church encodings (lib/Logic.wiz) that eliminate only into `Prop`.
  A proof of `∃ n, P n` can never hand a computation its `n`.
* numerals are kernel literals with native arithmetic, so the kernel computes with
  big numbers (`Sqrt2.d (10^20)` by `rfl`).
* there is no arithmetic library and no `ring`, `omega` or `simp` (FINDINGS.md, G2),
  and tactics can't read equations (G1).

## The construction: Bishop's regular sequences

A real number is a sequence `x : Nat → Q` with
`|xₘ - xₙ| ≤ 1/(m+1) + 1/(n+1)` (Bishop's `1/m + 1/n`, shifted to start at 0), and
`x ≈ y` when `|xₙ - yₙ| ≤ 2/(n+1)` for all `n`. Why this one:

* **No quotient is needed.** Equality is a setoid, which is how constructive analysis
  is written anyway (Bishop and Bridges); every operation comes with a congruence
  lemma. Wiz couldn't do otherwise: it has no quotients.
* **No modulus of convergence is needed.** A general Cauchy sequence needs, for each ε,
  an index N; as an `∃` that would be a `Prop`, which a computation can't use, and as a
  Σ it would have to be carried and composed everywhere. A regular sequence has the
  modulus built in (`1/(n+1)`), so `x.seq n` *is* the n-th approximation, and
  computing digits is just evaluation (`app/sqrt2.wiz`).
* **Dedekind cuts** would be predicates `Q → Prop`: easy to state with impredicative
  `Prop`, but nothing could be computed from them (no choice, `∃` is a Church
  encoding), and arithmetic on cuts is harder to prove.
* **Equality is decided where it can be.** The order on `Nat` is the Prelude's
  Boolean `Nat.le` (`Nat.Le m n := Nat.le m n = .true`), so many order facts are
  definitional and case splits use `Bool.cases`; the order on `Q` is decidable
  (`Q.le_or_lt`), which is what lets the archimedean lemma
  `Q.le_of_forall_le_add` be proved without classical logic.
* **Positivity is data.** `R.Pos x := (c : Q) × (0 < c) × ((n : Nat) → c - 1/(n+1) ≤ xₙ)`,
  a Σ in `Type` (Bishop's eventual positive lower bound, with the witness kept),
  because inverses and comparisons need the index and the bound. `R.NonNeg` is a
  proposition read at the shifted index `3n+2`; the shift is what makes it stable
  under `≈` and closed under `+` (see `src/Reals/RealOrder.wiz`).
* **Distances instead of an order on reals in the analysis.** `R.Dist x y e`
  (`|xₖ - yₖ| ≤ e + 2/(k+1)` for all k) is Bishop's characterisation of
  `|x - y| ≤ e`. Completeness and continuity are stated with it, which keeps every
  statement at the level of rationals and avoids nesting real-number operations.

The key lemma is **the equality criterion** `R.eq_of_bound` (and `R.dist_of_bound`):
if `|xₙ - yₙ| ≤ K/(n+1)` for some constant K, then `x ≈ y`. Every algebraic law of
the reals (associativity, distributivity, `√2·√2 = 2`) is proved by bounding the
distance of the two sequences at the same index by such a K, using regularity and
`1/(i+1) ≤ 1/(n+1)` for the larger indices that `+` and `·` use.

## The analysis layer, and where the IVT is allowed to use choice

`Reals.Complete` states completeness with `R.Dist`; `Reals.Analysis` adds the
distance algebra and the two forms of limit reasoning needed by a bisection:
pointwise-equal regular sequences have equal limits (`R.lim_congr`), and a
sequence that converges at rate `1/(n+1)` to `x` has `x` as its limit
(`R.lim_unique`). A `R.Nested` is a shrinking sequence of intervals: the lower
endpoints are a regular sequence, each interval `[loₙ, hiₙ]` has width at most
`1/(n+1)`, and the lower endpoints nest (`R.Dist (loₘ) (loₙ) ≤ 1/(m+1)`). Its
limit is `R.lim lo`, and both endpoints are close to it (`R.Nested.lo_dist`,
`R.Nested.hi_dist`).

The IVT is split at the constructive boundary. `R.Continuous f` is pointwise
continuity with a modulus returned as data, because the proof uses it. An
`R.Bracket f` is a `R.Nested` together with the sign certificate a bisection
maintains (`f(loₙ)ₖ ≤ 1/(k+1)`, `-1/(k+1) ≤ f(hiₙ)ₖ`) and the distance from the
upper endpoints to the limit. `R.ivt_approx` proves that the limit is a zero:
continuity at the limit plus the two one-sided bounds give `|f(x)ₖ| ≤ 3/(k+1)`,
and regularity improves 3 to the `2/(k+1)` of `R.Dist _ 0 0`.

What is deliberately not assumed is that the *bracket can be constructed* from
`f(a) < 0 < f(b)`. That would require deciding, at each midpoint, whether
`f(mid) ≤ 0` or `0 ≤ f(mid)`. `R.Le` is a `∀` over indices of a decidable rational
inequality and `R.Lt` is a `Σ`; neither is total, and deriving a decision from
`¬¬` would need Markov/choice. A classical layer could add a sign oracle and
construct the bracket; the Bishop core does not. The approximate-sign route (test
a rational approximation and carry a slack) avoids the oracle but is more index
bookkeeping; it is the natural next step, and `R.ivt_approx` is already the lemma
its limit step needs.

## The rationals

`Q` is a structure of an integer numerator, an integer denominator and a proof that the
denominator is positive; it is **not reduced**. `p ≈ q` is `p.num * q.den = q.num * p.den`.
Reducing by gcd would keep numbers small, but every law would then need facts about
gcd; unreduced fractions make every law an identity of integers. The sizes stay small
in practice because the reals only ever multiply two terms of their sequences, and
`√2`'s terms have denominator `n + 1`.

## Automation: three reflective normalisers

All the algebra is done by **proof by reflection** (since wiz #221 the normalisers are
Wiz's library, so the file names below are `lib/`'s):

* `nat_ring!` (lib/Ring.wiz): commutative semirings at `Nat`. Expressions over
  atoms are normalised into sorted lists of monomials; soundness is proved once.
* `int_ring!` (lib/IntRing.wiz): commutative rings at `Int`, with integer
  coefficients. Its soundness needs the ring laws of `Int`, which are proved through
  the pair representation (`Int.ofPair a b = a - b`, lib/IntRing.wiz) by a slower
  bootstrap normaliser, `int_pair_ring!`, on top of `nat_ring!`.
* `q_ring!` (lib/Rat.wiz): identities of rationals that hold in every
  commutative ring, up to `≈`. A rational expression has a numerator and a denominator
  that are integer expressions in its atoms' numerators and denominators; `lhs ≈ rhs`
  is one integer identity.

A term macro sees only its own syntax, so `nat_ring! lhs = rhs` repeats the equation it
proves. Where the equation is the goal, `by ring` (lib/RingTactic.wiz, wiz #227) reads
the goal instead; what is left of the macros here is the equations that are *arguments*
to a congruence (an `Int.Le.congr`, a `Q.lt_congr`, …), which no tactic can fill.

Chains of inequalities are written with every intermediate term spelled out
(`Q.chain a b c h₁ h₂`): letting the elaborator infer them is slow, and a mistake in
such a chain took minutes to be reported (S4).
