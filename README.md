# lean-proofs

Public, timestamped Lean 4 formalizations produced by **Ascent**, an AI research agent, with **Aaron Gregory** as the human owner of this repository.

These files may later be submitted to the Justin Sun Prize formalization track. They are recorded here as Ascent wrote them. They are not human-authored mathematics, and this README does not claim prize eligibility.

Toolchain: Lean 4 `v4.34.1` with mathlib pinned to tag `v4.34.1`. Build with:

```bash
lake exe cache get
lake build
```

GitHub Actions runs the same build on every push and pull request.

## Files

### `LeanProofs/ConsecutivePowerful.lean`

- **Main theorems:** `Ascent.not_consecutive_powerful_imp_square`, `Ascent.infinite_consecutive_powerful_nonsquare`
- **Status:** Proved (no `sorry`). Formalizes a **known** result, not a new theorem.

If two consecutive positive integers are powerful (every prime factor has exponent at least 2), must one of them be a square? In other words, do all consecutive powerful pairs arise from Pell equations of the form \(x^2 - d y^2 = \pm 1\), giving pairs like \((n^2-1, n^2)\)? The file answers **no**, in two strengths:

1. A single counterexample (Golomb 1970): \(12167 = 23^3\) and \(12168 = 2^3\cdot 3^2\cdot 13^2\), neither a square.
2. Infinitely many consecutive powerful pairs in which **neither** term is a square, via the Pell-type equation \(2X^2 - 23Y^2 = 1\) with seed \((X,Y)=(78,23)\) (so \(n = 23 Y^2\), \(n+1 = 2 X^2\)).

The infinite family is a theorem of Walker (1976). Walker’s published family is \(7^3 x^2 = 3^3 y^2 + 1\); this file uses a different explicit family seeded at Golomb’s pair.

An independent formalization of the Golomb counterexample (Erdős problem 365, “must one be a square?”) exists in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (`FormalConjectures/ErdosProblems/365.lean`). That repository does not, at the time of writing, contain the infinite-family argument.

Written by Ascent, 19 October 2026.

### `LeanProofs/PrimeSumRay.lean`

- **Main theorem:** `Ascent.erdos473_of_largePrimes`
- **Status:** Proved **conditionally**. Erdős problem 473 is **not** proved here. The number-theoretic hypothesis is an explicit argument, not an axiom.

Erdős #473 asks for a permutation of the positive integers in which every pair of consecutive terms sums to a prime. This file proves a combinatorial reduction:

- `hamiltonian_ray`: a connectivity hypothesis on a graph on \(\mathbb{N}\) yields a Hamiltonian ray (a bijection \(a : \mathbb{N} \to \mathbb{N}\) with adjacent terms adjacent in the graph).
- `erdos473_of_connected`: #473 follows if that connectivity holds for the prime-sum graph.
- `erdos473_of_largePrimes`: connectivity (hence #473) follows from `LargePrimesHypothesis`, a Goldbach-type statement left unproved and passed in as a hypothesis: every odd \(N\) can be written \(p + r = q + N\) with primes \(p,q,r\) all larger than any given bound.

### `LeanProofs/IMO2026P5.lean`

- **Main theorem:** `Ascent.IMO2026P5.imo2026_p5`
- **Status:** Full characterization of the solutions of IMO 2026 Problem 5. Proved (no `sorry`).

The functions \(f\) (modelled as \(f : \mathbb{R} \to \mathbb{R}\), required positive on positives) satisfying

\[
\sqrt{\frac{x^2 + f(y)^2}{2}} \ge \frac{f(x)+y}{2} \ge \sqrt{x\, f(y)}
\]

for all \(x,y > 0\) are exactly the shifts \(f(x) = x + c\) for a constant \(c \ge 0\).

Proof found by Ascent, 20 October 2026, before seeing any solution.

### `LeanProofs/IMO2026P6Reduction.lean`

- **Main theorem:** `Ascent.IMO2026P6.mem_range_iff`
- **Status:** **Partial progress only. Not a solution** of IMO 2026 Problem 6.

The greedy sequence (\(a(n+1)\) is the least integer above \(a n\) that shares a common factor with every earlier term; every term \(> 1\)) is shown to be pairwise non-coprime, and its range is exactly

\[
\{ m \ge a(0) \mid \forall i,\ \gcd(m, a(i)) > 1 \}.
\]

No periodicity is proved.

### `LeanProofs/IMO2026P6Conditional.lean`

- **Main theorem:** `Ascent.IMO2026P6.periodic_of_smallShared`
- **Status:** **Partial progress only, and conditional. Not a solution** of IMO 2026 Problem 6.

Includes the reduction above, then assumes an unproved hypothesis `SmallShared a B`: every two terms of the sequence share a prime factor \(\le B\). Under that hypothesis the sequence is periodic in the strong sense \(a(n+T) = a(n) + B!\) for some \(T > 0\). The hypothesis is an explicit argument, not an axiom, and is not proved here.

### `LeanProofs/MelfiCriterion.lean`

- **Main theorems:** `Melfi.weird_iff`, `Melfi.pseudoperfect_iff`, `Melfi.rep_iff_interval`
- **Status:** Proved (no `sorry`). Formalizes a known criterion (Melfi-type, for \(n = 2^k p q\)); does not prove Erdős #470.

For \(n = 2^k p q\) with \(p < q\) odd primes, write \(A\) via \(\sum\) of proper divisors of \(n\) equals \(n + A\). Under the side conditions \(A < p q\), \(A < p \cdot 2^{k+1}\), and \(q - p \le 2^{k+1}\),

\[
n\text{ is abundant and not pseudoperfect}
\quad\iff\quad
A > 0 \text{ and no integer } T < 2^{k+1} \text{ satisfies } pT \le A \le qT + 2^{k+1} - 1.
\]

The statements use Mathlib's own `Nat.Abundant` and `Nat.Pseudoperfect` (Mathlib's `Nat.Weird` is `Abundant ∧ ¬ Pseudoperfect`); `Melfi.weird_iff'` restates the same criterion as `Nat.Weird n ↔ …`. Sanity examples: 70 is weird, 572 is pseudoperfect.

A GitHub code search on Oct 27, 2026 (queries: Melfi, Pseudoperfect, Nat.Weird) found no other Lean formalization of this \(2^k\cdot p\cdot q\) criterion; google-deepmind/formal-conjectures `ErdosProblems/470.lean` states the open questions only.

This is a partial step toward [Erdős problem #470](https://www.erdosproblems.com/470) (infinitely many primitive weird numbers); it does **not** prove #470.

Written by Ascent, 26 October 2026.

### `LeanProofs/MelfiRegion.lean`

MelfiRegion.lean: an explicit region of primes p = 2^(k+2) - a, q = 2^(k+2) + b with 2^k p q weird (widens Melfi 2015 Thm 1; conditional route for Erdős #470, not a proof). AI-made by Ascent.

## Axioms

Each file ends with `#print axioms` on its main theorem(s). The intended axiom set is the standard classical trio: `propext`, `Classical.choice`, `Quot.sound`.
