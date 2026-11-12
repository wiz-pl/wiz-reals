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
* **Positivity is data.** `R.Pos x := (n : Nat) × (1/(n+1) < xₙ)`, a Σ in `Type`
  (Bishop's definition, with the witness kept), because inverses and comparisons
  need the index. `R.NonNeg` is a proposition.
* **Distances instead of an order on reals in the analysis.** `R.Dist x y e`
  (`|xₖ - yₖ| ≤ e + 2/(k+1)` for all k) is Bishop's characterisation of
  `|x - y| ≤ e`. Completeness and continuity are stated with it, which keeps every
  statement at the level of rationals and avoids nesting real-number operations.

The key lemma is **the equality criterion** `R.eq_of_bound` (and `R.dist_of_bound`):
if `|xₙ - yₙ| ≤ K/(n+1)` for some constant K, then `x ≈ y`. Every algebraic law of
the reals (associativity, distributivity, `√2·√2 = 2`) is proved by bounding the
distance of the two sequences at the same index by such a K, using regularity and
`1/(i+1) ≤ 1/(n+1)` for the larger indices that `+` and `·` use.

## The rationals

`Q` is a structure of an integer numerator, an integer denominator and a proof that the
denominator is positive; it is **not reduced**. `p ≈ q` is `p.num * q.den = q.num * p.den`.
Reducing by gcd would keep numbers small, but every law would then need facts about
gcd; unreduced fractions make every law an identity of integers. The sizes stay small
in practice because the reals only ever multiply two terms of their sequences, and
`√2`'s terms have denominator `n + 1`.

## Automation: three reflective normalisers

(Since wiz #221 these live in Wiz's library: lib/Ring.wiz, lib/IntRing.wiz, lib/Rat.wiz;
`by ring`, wiz #227, runs them on the goal. The file names below are those of
lib/.)

All the algebra is done by **proof by reflection**:

* `nat_ring!` (lib/Ring.wiz): commutative semirings at `Nat`. Expressions over
  atoms are normalised into sorted lists of monomials; soundness is proved once.
* `int_ring!` (lib/IntRing.wiz): commutative rings at `Int`, with integer
  coefficients. Its soundness needs the ring laws of `Int`, which are proved through
  the pair representation (`Int.ofPair a b = a - b`, lib/IntRing.wiz) by a slower
  bootstrap normaliser, `int_pair_ring!` (lib/IntRing.wiz), on top of
  `nat_ring!`.
* `q_ring!` (lib/Rat.wiz): identities of rationals that hold in every
  commutative ring, up to `≈`. A rational expression has a numerator and a denominator
  that are integer expressions in its atoms' numerators and denominators; `lhs ≈ rhs`
  is one integer identity.

They are term macros, not tactics, because tactics can't read an equation
(FINDINGS.md, G1): `int_ring! a * (b + c) = a * b + a * c` repeats the equation it
proves. They expand to `P.proveAt lhs rhs ρ e₁ e₂ rfl rfl rfl` (the type is the
equation as written; the `rfl`s check that the reified expressions evaluate to the
sides and that the normal forms agree), compare normal forms with a Boolean function
rather than `rfl` at a list type (S2), and avoid ascriptions (S3).

Chains of inequalities are written with every intermediate term spelled out
(`Q.chain a b c h₁ h₂`): letting the elaborator infer them is slow, and a mistake in
such a chain took minutes to be reported (S4).
