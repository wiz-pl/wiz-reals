# Findings

What building the real numbers in Wiz showed about the language, its kernel, its
elaborator, its tactics and its tooling, as of the toolchain in `wiz-toolchain`
(master `183f823`, 2026-11-11). Each entry says what happened, a minimal reproducer,
and what this project does instead. Severity:

* **bug**: wrong behaviour;
* **gap**: something real mathematics needs that Wiz doesn't have, so this project
  built it or worked around it;
* **papercut**: works, but costs time;
* **slow**: correct but slow (timings are wall-clock under `light` on a shared
  machine: approximate, not measurements).

## Status (2026-11-12)

Fixed in wiz PRs that are not merged yet. Branch `cleanup` of this repository uses them
(a local toolchain: master + #230 + #239 + #221 + #227) and drops the workarounds:

* **G2** (no arithmetic library): lib/Nat, Order, Ring (`nat_ring!`), Int, IntRing
  (`Int.ofPair`, `int_ring!`, `int_pair_ring!`), IntOrder and Rat (`Q`, its laws,
  `q_ring!`) are this project's modules, upstreamed in #221. On `cleanup`, src/Reals/{Nat,Order,Ring,Int,IntRing,ZRing,IntOrder,Rat,QRing,
  QLaws}.wiz are gone and the rest imports lib (`Nat.le_zero` is `Nat.zero_le`,
  `Nat.sub_add_of_le` is `Nat.add_sub_of_le`).
* **B1** (recursive calls don't insert implicits), **B3** (`Nat.toString` ≥ 2^64; app/sqrt2.wiz
  prints with it again), **P6** (two `let`s on a line), **P8** (`|>` on proofs), **P9**
  (errors repeated in every importer), **P12** (partially applied recursive calls):
  fixed in #239.
* **G1** (tactics can't read an equation): fixed by `TacticM.eqView` (#197); `by ring`
  (#227) is the normalisers as a tactic that reads the goal.
* **S1, S3, S4** (slow failures, slow ascribed proofs): fixed in #230 (one unfolding
  order per glued layer). S4's wrong proof is rejected in about 5 s with the type error.
* Not fixed: **B2** (proofs count usage; wiz agent prf-conv-2), **P1** (computed
  equations vs `Eq.trans`: glued equations, #155; the `@Eq.trans Int x y z` stay),
  **P7** (#214), **S2** (glued equations), **S5** (not reproduced with a reconstruction
  of the old Isqrt), P2–P5, P10, P11.

## Gaps

### G1. Tactics can't read an equation (fixed in wiz #197, #227)

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

Here: the decision procedures are **term macros** that reify the *syntax* of an
equation the user writes out again: `nat_ring! (a + b) * c = a * c + b * c`
(src/Reals/Ring.wiz) and `int_ring! …` (src/Reals/IntRing.wiz). The macro expands to
`(NE.prove ρ e₁ e₂ rfl : lhs = rhs)`, so the kernel checks the ascription by
conversion. It works well, but the equation has to be written twice (once in the
statement, once in the proof), and atoms are compared syntactically (`f x` and
`f (x)` are two atoms).
Wanted: `Expr.eq A a b` in the reflected terms (and in `Expr.view`).

### G2. No arithmetic library: everything from `0` and `succ` (upstreamed in wiz #221, #227)

lib/ has `Int` with five lemmas, no `Rat`, no order on `Nat` or `Int` as a
proposition, no `≤`/`<` notation, and no `ring`/`omega`/`linarith`/`simp`. Before the
first fact about rationals this project had to write: the commutative semiring laws of
`Nat` and its order (src/Reals/Nat.wiz), a reflective normaliser for commutative
semirings with its soundness proof (src/Reals/Ring.wiz), the ring laws of `Int`
through the pair representation (src/Reals/Int.wiz), a reflective normaliser for `Int`
on top of the one for `Nat` (src/Reals/IntRing.wiz) and the order of `Int`
(src/Reals/IntOrder.wiz). Upstream candidates: all of these (generic and checked).

## Bugs

### B1. A recursive call in an equation definition doesn't insert implicit arguments (fixed in wiz #239)

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
(src/Reals/Nat.wiz `Nat.add_right_cancel`, src/Reals/IntOrder.wiz `Int.NonNeg.congr`),
and transport motives taken at quantity 0.

### B3. `Nat.toString` fails on numbers of 2^64 and above (fixed in wiz #239)

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
`@Eq.trans Int x y z p q` with the three sides written out (src/Reals/IntOrder.wiz,
src/Reals/Ring.wiz `Poly.eval_const`).

### P2. A failed definition turns into confusing errors downstream

When `Key.insertB` fails to check, every later use reports
`unknown identifier 'Key'` (not `Key.insertB`), and a failed `Nat.add_left_cancel`
makes `Nat.add_left_cancel k h` report `no field 'add_left_cancel' in a value of type
Type` (the name falls back to field access on the type `Nat`).

### P3. `fun x => …` for an argument `P : A → Prop` with `A` implicit

`Eq.mp' (fun x => Nat.Le x (b + k)) e h` fails with "unification problem is outside the
pattern fragment"; `fun (x : Nat) => …` works.

### P4. Projections of an unsolved equation

`absurd (Eq.trans (Eq.symm h) (Nat.lt_zero n)).1` reports
`cannot project from a value of type ?m1 n h = ?m3 n h`; the implicits of `Eq.trans`
are solvable from its arguments, but `.1` is elaborated first. Here:
`Bool.trueNeFalse (…)` (lib/Logic.wiz).

### P5. No release snapshot of a recent master

Only one of the 30 newest master commits (183f823) had a release snapshot on
2026-11-12, so `wiz-toolchain` can't name the newest master (9596a24): tower fails
with a 404 and lists the retained snapshots. This project pins 183f823.

### P8. `|>` only pipes data (fixed in wiz #239)

`pipe {A B : Type}`, so `h |> fun h => …` with `h` a proof fails with "universe level
mismatch: 1 vs 0". Proof terms are written inside out.

### P9. A failing module's errors are repeated inside every importer's error (fixed in wiz #239)

When src/Reals/Ring.wiz had one error, checking src/Reals/QLaws.wiz (six imports
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

### P11. Numerals print as `OfNat.ofNat R 2 (instOfNatRN 2)`

`#check R.sqrt2_sq` prints `R.sqrt2 * R.sqrt2 ≈ OfNat.ofNat R 2 (instOfNatRN 2)`; at
`Nat` and `Int` numerals print as numerals. (tests/sqrt2.expected)

### P12. Partially applied recursive calls (fixed in wiz #239)

In a definition by equations with a parameter before the colon,
`Isqrt.step … (Isqrt.go n f) …` (the recursive function applied to the parameter and
the structural argument only) is rejected: "recursive call of Isqrt.go on n, which is
not a recursive field". Eta-expanding, `(fun a b => Isqrt.go n f a b)`, works.

## Slowness

### S1. A unification failure under a binder takes 17–80 s (fixed in wiz #230)

```
import Reals.Int
def r (a b c d : Nat) : Int.ofPair a b + -(Int.ofPair c d) = Int.ofPair (a + d) (b + c) :=
  Eq.trans (congrArg (fun y => Int.ofPair _ _ + y) (Int.ofPair_negate _ _)) (Int.ofPair_add _ _ _ _)
```

fails after 17 s ("outside the pattern fragment": the holes under `fun y` become
`?m a b c d y`). The same shape in the `.sub` case of `IE.sound`
(src/Reals/IntRing.wiz, first version) took 80 s to fail. Writing the arguments out (a
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
identity with 36 monomials ran out of memory. Here: `Poly.beq`/`ZPoly.beq` and a
soundness lemma (`Poly.beq_eval`), in src/Reals/Ring.wiz and src/Reals/ZRing.wiz.

### S3. The same proof is 8× slower under an ascription (fixed in wiz #230)

```
import Reals.QRing
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
the equation is the expected type (src/Reals/Ring.wiz, `Reify.expandWith`).

### P6. `let a := …; let b := …;` on one line ends the term (fixed in wiz #239)

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

### S4. A wrong proof in a chain of inequalities takes minutes to be rejected (fixed in wiz #230)

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

## How long things take

On this machine, under `light`/`heavy` (approximate): every module checks in 1–16 s
once written correctly; `grail build` from scratch about 95 s, most of it the
reflective `rfl`s of `q_ring!` in src/Reals/QLaws.wiz and the reals. A single
`q_ring!` identity with four atoms takes about 1 s (S3 explains why not 20 s).
The cost of writing is dominated by S4: a wrong step is a timeout, not an error.

## What is missing

* **The inverse of a real apart from zero** (Bishop's `x⁻¹` with `x_{N²(n+1)}`) and the
  field law `x · x⁻¹ ≈ 1`. All the pieces exist (positivity as data, `Q.inv`, the
  equality criterion); it is the same kind of index bookkeeping as `R.mul_assoc`.
* **The intermediate value theorem** (approximate form). Continuity is stated
  (`R.add_dist`, `R.mul_dist`) but not for general functions.
* **The order on reals beyond the basics**: positivity, non-negativity, `R.archimedean`
  and `|x|` are there; transitivity of `<` and compatibility with `+` and `·` are not.

## Not written in Wiz

Nothing in the package. While developing, a small Python script checked growing
prefixes of a file with a time limit, to find the definition that made the checker
hang (S4, S5).
