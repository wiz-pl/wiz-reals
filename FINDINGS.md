# Findings

What building the real numbers in Wiz showed about the language, its kernel, its
elaborator, its tactics and its tooling, as of the toolchain in `wiz-toolchain`
(master `4ad29792`, 2026-11-18). Each entry says what happened, a minimal reproducer,
and what this project does instead. Severity:

* **bug**: wrong behaviour;
* **gap**: something real mathematics needs that Wiz doesn't have, so this project
  built it or worked around it;
* **papercut**: works, but costs time;
* **slow**: correct but slow (timings are wall-clock under `light` on a shared
  machine: approximate, not measurements).

## Status at the pinned toolchain (2026-11-18)

`wiz-toolchain` names master `4ad29792` (the same commit as `flake.nix`/`flake.lock`).
This project's arithmetic modules were upstreamed in wiz #221, so the local copies are
gone: `src/Reals/{Nat,Order,Ring,Int,IntRing,ZRing,IntOrder,Rat,QRing,QLaws}.wiz` were
deleted and the rest imports `lib/` (`Nat.le_zero` is `Nat.zero_le`, `Nat.sub_add_of_le`
is `Nat.add_sub_of_le`).

At that commit: **P3** is still open — `lib/`'s `Eq.mp'`/`Eq.mpr'` take the motive
before the equation, so a bare `fun x => …` fails; every use annotates its binder, and
`tests/p3.wiz` is gone (`repro/p3-motive-first.wiz` pins the error). **P4** is
reproduced with a minimal trigger (`repro/p4-proj-trans.wiz`) and worked around
(`tests/p4.wiz`); **P5**: this pin has a release snapshot; **P11** is fixed by wiz #202
(`tests/sqrt2.expected` prints `≈ 2`). B2, P1, P2, P7, P10 and S2 are unchanged.

## Gaps

### G1. Tactics can't read an equation (fixed by wiz #197; `by ring` in #227)

`TacticM.goalType` reflects `a = b` as `Expr.opaque _` (the reflected `Expr` has no
constructor for the kernel's equality; Prelude: "Kernel forms with no constructor here
(μ, descriptions, equality, sizes, …) are `opaque` handles"). Every goal of algebra is
an equation, so a `ring` tactic that looks at its goal can't be written.

```
import Prelude
syntax (name := showGoal) "show_goal" : tactic
def Expr.dbg : Expr → String
  | .app f a => "(" ++ Expr.dbg f ++ " " ++ Expr.dbg a ++ ")"
  | .const n => n
  | .opaque _ => "opaque"
  | _ => "…"
def showGoalT : Tactic := fun _ => do
  g ← TacticM.mainGoal;
  t ← TacticM.goalType g;
  TacticM.trace (Expr.dbg t)
attribute [tactic tactic.showGoal] showGoalT
def t1 (a b : Nat) : a + b = a + b := by
  show_goal       -- info: opaque
  exact rfl
```

This project used to carry **term macros** that reify the *syntax* of an equation the
user wrote out again. `TacticM.goalType` now reflects an equation (`TacticM.eqView`),
and `by ring` (lib/RingTactic.wiz) reads the goal, so the normalisers live in lib
(lib/Ring.wiz, lib/IntRing.wiz, lib/Rat.wiz) and the macros are only used where the
equation is an *argument* to a congruence, which no tactic can fill.

### G2. No arithmetic library: everything from `0` and `succ` (upstreamed in wiz #221)

lib/ has `Int` with five lemmas, no `Rat`, no order on `Nat` or `Int` as a
proposition, no `≤`/`<` notation, and no `ring`/`omega`/`linarith`/`simp`. Before the
first fact about rationals this project had to write: the commutative semiring laws of
`Nat` and its order (lib/Nat.wiz), a reflective normaliser for commutative
semirings with its soundness proof (lib/Ring.wiz), the ring laws of `Int`
through the pair representation (lib/IntRing.wiz), a reflective normaliser for `Int`
on top of the one for `Nat` (lib/IntRing.wiz) and the order of `Int`
(lib/IntOrder.wiz). Upstream candidates: all of these (generic and checked).

## Bugs

### B1. A recursive call in an equation definition doesn't insert implicit arguments

```
import Logic
def f : (k : Nat) → {m : Nat} → m = m → Nat
  | .zero, _, _ => 0
  | .succ k, _, e => f k e
-- error: type mismatch  expected: Nat  inferred: m = m
```

Inside its own equations, `f` behaves as if `{m}` were explicit; `@f k _ e` works.
(Outside, `f 3 rfl` is fine.) Related: implicit binders after the colon *are*
patterns (`| .zero, _, _ => …` needs the `_` for `{m}`), unlike Lean 4; fine, but
undocumented. For `Syn.beq : {ω b c : Bool} → SyntaxF b → SyntaxF c → Bool` even
`@Syn.beq _ _ xs ys` failed ("expected Bool, inferred SyntaxF .false"); it is a
`partial def` here.

### B2. Quantity 0 is enforced inside proofs, and the error comes from the kernel

Implicit binders default to quantity 0. In a proof (a term whose type is a `Prop`) a
0-variable can't be passed to an explicit argument:

```
import Logic
def p (k : Nat) (e : k = k) : k = k := e
def q {k : Nat} (e : k = k) : k = k := p k e
-- error: kernel rejected q: variable k declared with quantity 0 but used ω
```

All of `q` is a proof, so it is erased anyway; CoreSpec §11.5 already says quantities
don't matter in a Π that is a proposition. The elaborator lets it through and the
kernel rejects the finished declaration, so the message points at the declaration,
not at the use. Here: `{ω m n k : Nat}` on lemmas that use their implicits
(lib/Nat.wiz `Nat.add_right_cancel`, lib/IntOrder.wiz `Int.NonNeg.congr`),
and transport motives taken at quantity 0.

### B3. `Nat.toString` fails on numbers of 2^64 and above

`Nat` is arbitrary precision (GMP) in compiled code, but `Nat.toString` (lib/IO.wiz) is
`extern "wiz_nat_show"`, which takes a `uint64_t`:

```
import IO
def main : IO Unit := IO.println (Nat.toString (Nat.pow 10 30))
-- the program failed (3): wiz: a number is too big for a C integer
```

The arithmetic itself is fine (`Nat.lt (10^30) (10^31)` and `Nat.isqrt` on 121-digit
numbers run). Here: `Syntax.decimal` from the Prelude (app/sqrt2.wiz).

## Papercuts

### P1. Equations that have computed defeat `Eq.trans`

An equation at a data type whose sides are constructor-headed computes at once (OTT):
`Int.abs x = Int.abs y` is `Int.ofNat (natAbs x) = Int.ofNat (natAbs y)`, which is a Σ
of the payload's equations. `Eq.trans p q` then can't solve its middle implicit:

```
-- Int.abs a := Int.ofNat (Int.natAbs a)
def Int.abs_sub_comm (a b : Int) : Int.abs (a - b) = Int.abs (b - a) :=
  Eq.trans (congrArg Int.abs (int_ring! a - b = -(b - a))) (Int.abs_neg (b - a))
-- expected: Int.abs (- (b - a)) = ?m9 a b
-- inferred: (0 e : Int.natAbs (- (b - a)) = Int.natAbs (b - a)) × (0 e' : True) × True
```

Same with `Nat.succ n * 1 = Nat.succ n` (it is `n * 1 = n`). Here:
`@Eq.trans Int x y z p q` with the three sides written out (lib/IntOrder.wiz,
lib/Ring.wiz `Poly.eval_const`).

### P2. A failed definition turns into confusing errors downstream

When `Key.insertB` fails to check, every later use reports
`unknown identifier 'Key'` (not `Key.insertB`), and a failed `Nat.add_left_cancel`
makes `Nat.add_left_cancel k h` report `no field 'add_left_cancel' in a value of type
Type` (the name falls back to field access on the type `Nat`).

### P3. `fun x => …` for an argument `P : A → Prop` with `A` implicit (still open)

`Eq.mp' (fun x => Nat.Le x (b + k)) e h` fails with "a variable escapes the scope of
the hole being solved" (an earlier toolchain reported "unification problem is outside
the pattern fragment"). The same shape in a helper of its own:

```
import Nat
def Eq.mpMotiveFirst {A : Type} {a b : A} (0 P : A → Prop) (e : a = b) (h : P a) : P b :=
  Eq.substProp P e h
def t (a b k : Nat) (e : a = b) (h : Nat.Le a (b + k)) : Nat.Le b (b + k) :=
  Eq.mpMotiveFirst (fun x => Nat.Le x (b + k)) e h
-- error: type mismatch  expected: ?m9 a b k e h a  inferred: Nat.Le a (b + k)
--   (a variable escapes the scope of the hole being solved)
```

Root cause (Wiz `checkApp`): the motive lambda is postponed, because its binder's
type is the hole `?A` (`postponable`/`unknownDomains`), but the later argument
`h : P a` is elaborated in the same pass, before the postponed lambda. Its expected
type `?P a` makes the unifier solve the placeholder `?P` from `h`'s type in the
extended context (`?m9 a b k e h a`), and the solution mentions a variable outside
the hole's scope. With the *equation* first, `?A` is solved from `e` before the
motive is elaborated, so a bare lambda works.

At this pin lib's `Eq.mp'`/`Eq.mpr'` (lib/Nat.wiz) take the motive first, which is the
failing order, so every use in the reals annotates the binder:
`Eq.mp' (fun (z : Nat) => …) e h` (src/Reals/{Isqrt,QSeq,Sqrt2}.wiz). That was the
one place the project's own `Eq.mp'` (equation first, now upstream with the other
order) made bare lambdas work; this repository has no `tests/p3.wiz` any more.
`repro/p3-motive-first.wiz` pins the error above, so a fix in Wiz shows up as that test
failing. Where the equation's type is itself a computed equation (at `Q`, a structure),
the arguments stay explicit (`@Eq.mp' Q p q …` in lib/Rat.wiz `Q.ofEq`): the equation
first would have to unify the computed Σ with an equation whose sides are still holes.
The general fix is to postpone an argument whose domain mentions a postponed
placeholder.

### P4. Projections of an unsolved equation (reproduced; workaround)

`absurd (Eq.trans (Eq.symm h) (Nat.lt_zero n)).1` reports `cannot project from a value
of type ?m1 n h = ?m3 n h`: the implicits of `Eq.trans` are solvable from its arguments,
but `.1` is elaborated first. The minimal trigger has no arithmetic in it — an equation
of booleans (`repro/p4-proj-trans.wiz`, whose expected output is the error):

```
import Logic
def t (b : Bool) (h : Bool.true = b) (k : b = Bool.false) : False :=
  absurd (Eq.trans h k).1
```

Root cause (`Wiz/Elab/Term.lean`, `term.proj`): the projected term is *inferred* with no
expected type, then the type is forced once and its head is matched against `Σ`. For
`Eq.trans h k` the type at that moment is still the neutral equation `?m1 b h k = ?m3 b h k`
(the application's implicit sides are not solved yet; `inferApp` returns the type value
before it is zonked), so `elabProj` reports "cannot project" instead of seeing the Σ that
an equation of booleans computes to. The same term *checked* against an expected type
(elaborated by `checkApp`, which unifies the expected type with the application's type
first) has its sides solved; storing the term in a `let` also works, because `elabLet`
quotes the inferred type (`quote` zonks the spine) before the body is checked.

Here: the equation is given as the expected type — an ascription (`(… : Bool.true =
Bool.false)`, or a hole `: _`), or a lemma whose domain is that equation, which is what
lib/Logic.wiz's `Bool.trueNeFalse` does (`Bool.trueNeFalse (Eq.trans (Eq.symm h) (Nat.lt_zero n))`,
lib/Nat.wiz `Nat.not_succ_le_zero`). tests/p4.wiz proves the finding's statements
with each form; no statement is weakened. A fix in Wiz would be to zonk the inferred
type (or solve the application's pending sides) before matching the head in `term.proj`.

### P5. No release snapshot of the newest master (this pin has one)

Not every master commit has a release snapshot, so `wiz-toolchain` cannot always name
the newest one: tower fails with a 404 and lists the retained snapshots. `4ad29792` has
one (2026-11-18), so the pin is installable with tower's release source.

### P8. `|>` only pipes data (fixed in wiz #239)

`pipe {A B : Type}`, so `h |> fun h => …` with `h` a proof fails with "universe level
mismatch: 1 vs 0". Proof terms are written inside out.

### P9. A failing module's errors are repeated inside every importer's error

When lib/Ring.wiz had one error, checking lib/Rat.wiz (six imports
further) printed one line per importer, each containing the whole nested list of
the errors below it: several kilobytes of `module Reals.X has errors: [module
Reals.Y has errors: [...]]` and the 'no field' cascades of P2, for one typo.

### P10. Equations that compute meet class methods

`Q.ofNat (k + 2) ≈ Q.ofNat k + 2` unfolds (through `Equiv.equiv`, `Q.Eq`, `Int.mul` of
`Int.ofNat`s) to an equation of `Int.ofNat`s, which computes to a Σ whose first field
is an equation of naturals. Neither `nat_ring!` (an equation of naturals) nor
`congrArg Int.ofNat (nat_ring! …)` is accepted for it ("spine length mismatch": the
unifier compares the class method's application with the Σ instead of unfolding it).
`int_ring!` fails too, with "expected ?m30 p, inferred Int". What works: a separate
lemma whose type is the integer equation written out, proved by
`congrArg Int.ofNat (nat_ring! …)`, then used at `≈` (src/Reals/Real.wiz
`Q.ofNat_add2'`, src/Reals/Sqrt2.wiz `Sqrt2.err_eq'`).

### P11. Numerals print as `OfNat.ofNat R 2 (instOfNatRN 2)` (fixed in wiz #202)

`#check R.sqrt2_sq` used to print `R.sqrt2 * R.sqrt2 ≈ OfNat.ofNat R 2 (instOfNatRN 2)`;
at `Nat` and `Int` numerals already printed as numerals. At the pinned toolchain
(`4ad29792`, which has #202) it prints `≈ 2`, and tests/sqrt2.expected records that.

### P12. Partially applied recursive calls

In a definition by equations with a parameter before the colon,
`Isqrt.step … (Isqrt.go n f) …` (the recursive function applied to the parameter and
the structural argument only) is rejected: "recursive call of Isqrt.go on n, which is
not a recursive field". Eta-expanding, `(fun a b => Isqrt.go n f a b)`, works.

### P13. A projected structured field in a large expected type does not elaborate

While proving the upper and lower endpoint bounds for `R.ivt_approx`, the same
proof finished in seconds with the width as a *hypothesis* but timed out under
`light` when the width came from the structure field:

```wiz
def t (N : R.Nested) (n : Nat) (hw : R.Dist (N.hi n) (N.lo n) (Q.invS n)) : … := …
-- `hw` is fine; `N.width n` at the same place is not (180 s, no error)
```

`R.Nested.width : (n : Nat) → R.Dist (lo n) (hi n) (Q.invS n)` mentions the
structure's other fields, and matching its result against an expected
`R.Dist (N.hi n) (R.Nested.lim N) …` appears to unfold the structure instead of
projecting it. Here: `R.Bracket` carries `hi_close` as its own field, so the
lower-endpoint proof projects a plain hypothesis, and `R.Nested.hi_dist` is used
only where the expected type is small. A minimal standalone reproducer would be
useful; the workaround is cheap and keeps every proof checked.

## Slowness

### S1. A unification failure under a binder takes 17–80 s

```
import IntRing
def r (a b c d : Nat) : Int.ofPair a b + -(Int.ofPair c d) = Int.ofPair (a + d) (b + c) :=
  Eq.trans (congrArg (fun y => Int.ofPair _ _ + y) (Int.ofPair_negate _ _)) (Int.ofPair_add _ _ _ _)
```

fails after 17 s ("outside the pattern fragment": the holes under `fun y` become
`?m a b c d y`). The same shape in the `.sub` case of `IE.sound`
(lib/IntRing.wiz, first version) took 80 s to fail. Writing the arguments out (a
lemma `Int.ofPair_sub`) makes the whole file check in about 3 s, so the time goes into
the failure, probably into unfolding `Int.ofPair` (a `match` on `Nat.sub`) while
trying to unify.

### S2. `rfl` on two equal closed lists blows up

An equation of two closed values of a data type computes (OTT) into a Σ of the
equations of their parts, with casts for the later fields. For computed lists this is
far more expensive than comparing them:

```
import Int
def ins (x : Nat) : List Nat → List Nat
  | .nil => .cons x .nil
  | .cons y ys => if Nat.le x y then .cons x (.cons y ys) else .cons y (ins x ys)
def sort : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => ins x (sort xs)
def mk : Nat → List Nat
  | .zero => .nil
  | .succ n => .cons (Nat.mod (n * 7) 13) (mk n)
def chk : sort (mk 36) = List.append (sort (mk 36)) .nil := rfl
```

N = 12: 0.4 s; N = 24: 4.9 s; N = 36: killed by `light` at 2 GB. The same check
through a Boolean `lbeq (sort (mk 36)) (…) = .true := rfl` takes 0.5 s. This is how
the reflective provers first compared normal forms (`rfl : norm a = norm b`): an
identity with 36 monomials ran out of memory. Here: `NatPoly.beq`/`IntPoly.beq` and a
soundness lemma (`NatPoly.beq_eval`), in lib/Ring.wiz and lib/IntRing.wiz.

### S3. The same proof is 8× slower under an ascription

```
import Rat
-- 1.3 s:
def xI (p q r : Q) : p + q + r ≈ p + (q + r) :=
  QE.prove (List.cons p (List.cons q (List.cons r List.nil)))
    (QE.add (QE.add (QE.atom 0) (QE.atom 1)) (QE.atom 2)) (QE.add (QE.atom 0) (QE.add (QE.atom 1) (QE.atom 2))) rfl
-- 9.7 s: the same term as `(… : p + q + r ≈ p + (q + r))`
-- 9.6 s: as `let h : p + q + r ≈ p + (q + r) := …; h`
-- 11 s:  as `the (p + q + r ≈ p + (q + r)) (…)` with `def the (T : Prop) (t : T) : T := t`
-- 1.4 s: as the first component of a pair whose type is given
```

With four atoms (`p + q + r + s ≈ p + (q + (r + s))`) the ascribed form takes 20 s.
It looks as if, when the term is elaborated first and its type
`QE.eval ρ e₁ ≈ QE.eval ρ e₂` is then unified with the stated type, the elaborator's
unifier unfolds the evaluator very inefficiently, while the kernel (which checks both
versions) is fast. Here: the macros emit the bare proof, so they are only used where
the equation is the expected type (lib/Ring.wiz, `Reify.expandWith`).

### P6. `let a := …; let b := …;` on one line ends the term

```
  let ha := QE.sound ρ a; let hb := QE.sound ρ b;
  Eq.trans (congrArg2 …) (…)
```

parses the body as `Eq.trans` alone ("expected 'def', …" at the first argument, and a
type mismatch for the unapplied `Eq.trans`). One `let` per line works.

### P7. `-1 * 1 * x` at `Int` asks for `Neg Nat`

In `-(ZPoly.eval ρ p) = -1 * 1 * ZPoly.eval ρ p` the subterm `-1 * 1` has only
numerals, gets the default type `Nat`, and fails ("failed to synthesize an instance of
Neg Nat"); `-1 * x` is fine. Here: `(-1 : Int) * 1 * …` (the reifier looks through
ascriptions).

### S4. A wrong proof in a chain of inequalities takes minutes to be rejected

In `R.add_assoc` (src/Reals/Real.wiz), a congruence was used in the wrong direction:
`Q.le_congr (Q.abs_congr e) (Q.refl _) h` where `Q.le_congr` wanted `Q.symm (…)`. The
right proof checks in 1.5 s; the wrong one did not produce its type error within
180 s (`light`'s limit; the first version of `R.eq_of_bound` did the same). The
unifier, failing to match `Q.abs (a + b + c - (d + (b + e)))` against
`Q.abs (a + c - (d + e))`, apparently unfolds `Q.add`/`Q.sub` (each of which uses its
arguments twice, in the numerator and the denominator) into ever larger integer
terms instead of failing at the first rigid mismatch. In practice this means a
typo costs a three-minute wait and no error message; the workaround is to bisect by
hand (a script that checks growing prefixes of the file with a 60 s limit).

### S5. Unfolding a recursive definition against its own body: over a minute

`Isqrt.go n (succ f) lo hi` unfolds to a `Isqrt.stop …` term with a lambda that
contains the recursive call. Proving a lemma about it by giving the lemma about that
`stop` term (`Isqrt.stop_spec … rfl`) did not finish in 60 s. Moving the body into a
definition of its own, `Isqrt.body n g lo hi` with the recursive call as the argument
`g`, made the same proof check in under a second (src/Reals/Isqrt.wiz).

### S6. A `Nat` recursion over big values is ~100× slower at master `4ad29792` (blocks the √2 tests)

The same Prelude-only bisection loop as `src/Reals/Isqrt.wiz` (`mid`/`stop`/`step`/
`body`/`go`, fuel 100, returning `Nat.pow 10 12`):

```
def t : go 1000000000000000000000000 100 0 1000000000000000000000001 = 1000000000000 := rfl
```

checks in 1 s on `50cd3e7` and 134 s on `4ad29792`; at `n = 10^40` (the size the √2
digits need, `isqrt (2 · 10^40)`) it exceeds 300 s, while the whole of
`tests/sqrt2.wiz` took 6 s on `50cd3e7`. On the new pin, the same loop with fuel 100
takes 0 s at `n = 10^12`, 2 s at `10^18` and 134 s at `10^24`, so the cost grows with
the *numbers*, not the iteration count (the loop converges in about 40–80 rounds).
`Nat.div`, `Nat.lt` and `Nat.le` on the same big numbers, and a single `mid` call, are
each fast in isolation, and the compiled test `tests/digits.wiz` (which runs
`Sqrt2.d (10^20)`) passes, so the cost is in kernel evaluation of the recursion.

Consequence at this pin: `tests/sqrt2.wiz` times out (300 s) and `app/sqrt2.wiz`
times out its build job (1800 s). Everything else checks and tests green. The pin is
kept for the rest of the bump, but this repository's √2 test cannot pass on
`4ad29792` until the toolchain's evaluation of the loop returns to its old cost.

## How long things take

On this machine, under `light`/`heavy` (approximate): every module checks in 1–16 s
once written correctly; `grail build` from scratch about 95 s, most of it the
reflective `rfl`s of `q_ring!` in lib/Rat.wiz and the reals. A single
`q_ring!` identity with four atoms takes about 1 s (S3 explains why not 20 s).
The cost of writing is dominated by S4: a wrong step is a timeout, not an error.

## What is missing

**P0 status (after this slice).** Closed: `Nat.isqrt_eq_iff` (and `le_isqrt`,
`isqrt_lt`, `sqrt_add_eq`, `isqrt_mul_self`), `Q.invS_add_le`/`Q.invS_lt`, and the
first part of the real order (`R.le_refl`, `R.le_trans`, `R.nonneg_seq`,
`R.nonneg_congr`, `R.nonneg_add`, `R.nonneg_of_pos`, `R.abs_nonneg`). The new
`R.Pos` is a uniform rational lower bound `c - 1/(n+1) ≤ xₙ`; `R.NonNeg` reads its
sequence at `3n+2`, because the pointwise index made `NonNeg` neither stable under
`≈` nor closed under `+` (two one-sided `-1/(n+1)` bounds add to `-2/(n+1)`).

Deferred, with the timeboxed attempts in `timebox/order-deferred.md`:

* **`R.add_le_add` and `R.le_antisymm`.** `R.Le` is `R.NonNeg (y - x)`, so the
  index telescopes through `R.add`; the remaining step is an OTT equality of the
  `Q` structure (a Σ), not the `Q.Eq` that `q_ring!`/`Q.ofEq` expect. Both proofs
  were stopped at 180 s rather than left half-checking.
* **`R.mul_le_mul`, `R.abs_triangle`, `R.le_of_forall_pos`, `R.lt_cotrans`**:
  they depend on the two order lemmas above (or on the multiplication order).
* **The inverse of a real apart from zero** and the field law `x · x⁻¹ ≈ 1`.
  `R.Pos` now gives the uniform tail bound an inverse needs, so this is unblocked
  in shape; the reciprocal sequence and its regularity are not written.
* **Constructing the IVT bisection certificate.** `Reals.Analysis` proves the
  analysis half: `R.lim_congr`, `R.lim_unique`, the nested-interval API
  (`R.Nested`), and `R.ivt_approx`: if a continuous `f` comes with an `R.Bracket`
  whose lower endpoints satisfy `f(loₙ)ₖ ≤ 1/(k+1)`, whose upper endpoints satisfy
  `-1/(k+1) ≤ f(hiₙ)ₖ`, and whose upper endpoints stay within `2/(n+1)` of the
  limit, then `f` is zero at `R.Nested.lim`. What is *not* written is the
  construction of that bracket from `R.Lt (f a) 0` and `R.Lt 0 (f b)`. That step is
  the located sign test: at each midpoint it decides `f(mid) ≤ 0` or `0 ≤ f(mid)`.
  `R.Le`/`R.Lt` are not total (DESIGN.md), so this needs either a sign oracle or
  Bishop's approximate-sign bookkeeping (compare a rational approximation and keep
  a slack); it is the constructive/classical boundary, not a missing algebra lemma.
  The theorem is stated with `R.Dist`, so no `add_le_add`/`le_antisymm` was needed.
  `R.Nested` stores the width as `R.Dist (lo n) (hi n) (1/(n+1))`; the sign
  certificate `R.Bracket` also carries `hi_close`, the distance from `hi n` to the
  limit, because elaborating the field projection `R.Nested.width` at a large
  expected type did not finish (P13).

## Not written in Wiz

Nothing in the package. While developing, a small Python script checked growing
prefixes of a file with a time limit, to find the definition that made the checker
hang (S4, S5).
