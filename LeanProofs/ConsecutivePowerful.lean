import Mathlib

/-!
# Consecutive powerful numbers, neither a square (JSP-000301 / Erdős #365 side question)

Catalog question (JSP-000301): if two consecutive positive integers are powerful, must at
least one be a perfect square?  Answer: no (Golomb 1970).  We prove

* `not_consecutive_powerful_imp_square`: the catalog's yes/no question is false, witness
  `12167 = 23^3`, `12168 = 2^3 * 3^2 * 13^2`;
* `infinite_consecutive_powerful_nonsquare` (stronger): infinitely many `n` with `n`, `n+1`
  both powerful and neither a square, via the Pell-type equation `2X^2 - 23Y^2 = 1` and the
  unit `24335 + 3588√46` (note `23 ∣ 3588`), with `n = 23Y^2`, `n+1 = 2X^2`.

Written by Ascent (an AI agent), Oct 19 2026. Not submitted anywhere.
-/

namespace Ascent

/-- `n` is powerful if every prime dividing it divides it at least twice. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- If `q` is prime and `q ∣ Y`, then `q * Y^2` is powerful. -/
lemma powerful_prime_mul_sq {q Y : ℕ} (hq : q.Prime) (hqY : q ∣ Y) : Powerful (q * Y ^ 2) := by
  intro p hp hdvd
  rcases (Nat.Prime.prime hp).dvd_mul.mp hdvd with h | h
  · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    subst hpq
    have : p ∣ Y ^ 2 := dvd_pow hqY two_ne_zero
    rw [pow_two]
    exact mul_dvd_mul_left p this
  · have hpY : p ∣ Y := (Nat.Prime.prime hp).dvd_of_dvd_pow h
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpY 2) q

/-- A prime times a nonzero square is not a square. -/
lemma not_isSquare_prime_mul_sq {q Y : ℕ} (hq : q.Prime) (hY : Y ≠ 0) : ¬ IsSquare (q * Y ^ 2) := by
  rintro ⟨k, hk⟩
  have hYk : Y ∣ k := by
    have : Y ^ 2 ∣ k ^ 2 := by
      rw [pow_two k, ← hk]; exact Dvd.intro_left q rfl
    exact (Nat.pow_dvd_pow_iff two_ne_zero).mp this
  obtain ⟨m, rfl⟩ := hYk
  have hY2 : 0 < Y ^ 2 := by positivity
  have : q = m * m := by
    have h' : q * Y ^ 2 = (m * m) * Y ^ 2 := by rw [hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hY2 h'
  exact (Nat.Prime.prime hq).irreducible.not_isSquare ⟨m, this⟩

/-- The catalog question, answered negatively. -/
theorem not_consecutive_powerful_imp_square :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  -- 12167 = 23 * 23^2, 12168 = 2 * 78^2
  have h1 : Powerful 12167 := by
    have := powerful_prime_mul_sq (q := 23) (Y := 23) (by norm_num) dvd_rfl
    simpa using this
  have h2 : Powerful (12167 + 1) := by
    have := powerful_prime_mul_sq (q := 2) (Y := 78) Nat.prime_two (by norm_num)
    simpa using this
  rcases h 12167 (by norm_num) h1 h2 with hs | hs
  · exact not_isSquare_prime_mul_sq (q := 23) (Y := 23) (by norm_num) (by norm_num)
      (by simpa using hs)
  · exact not_isSquare_prime_mul_sq (q := 2) (Y := 78) Nat.prime_two (by norm_num)
      (by simpa using hs)

/-- One step of the Pell recursion: multiply `X√2 + Y√23` by `24335 + 3588√46`. -/
def step (p : ℕ × ℕ) : ℕ × ℕ :=
  (24335 * p.1 + 23 * 3588 * p.2, 24335 * p.2 + 2 * 3588 * p.1)

/-- The sequence of solutions, starting from `(78, 23)`. -/
def sol : ℕ → ℕ × ℕ
  | 0 => (78, 23)
  | k + 1 => step (sol k)

/-- Invariants: `2X^2 = 23Y^2 + 1`, `2 ∣ X`, `23 ∣ Y`, and `k + 23 ≤ Y`. -/
lemma sol_spec (k : ℕ) :
    2 * (sol k).1 ^ 2 = 23 * (sol k).2 ^ 2 + 1 ∧ 2 ∣ (sol k).1 ∧ 23 ∣ (sol k).2 ∧
      k + 23 ≤ (sol k).2 := by
  induction k with
  | zero => refine ⟨by norm_num [sol], by norm_num [sol], by norm_num [sol], by simp [sol]⟩
  | succ k ih =>
    obtain ⟨hpell, hX, hY, hle⟩ := ih
    simp only [sol, step]
    set X := (sol k).1
    set Y := (sol k).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hz : (2 : ℤ) * X ^ 2 = 23 * Y ^ 2 + 1 := by exact_mod_cast hpell
      have : (2 : ℤ) * (24335 * X + 23 * 3588 * Y) ^ 2
          = 23 * (24335 * Y + 2 * 3588 * X) ^ 2 + 1 := by
        linear_combination (24335 ^ 2 - 46 * 3588 ^ 2 : ℤ) * hz
      exact_mod_cast this
    · exact dvd_add (Dvd.dvd.mul_left hX _) (Dvd.dvd.mul_right (by norm_num : 2 ∣ 23 * 3588) Y)
    · exact dvd_add (Dvd.dvd.mul_left hY _) (Dvd.dvd.mul_right (by norm_num : 23 ∣ 2 * 3588) X)
    · omega

/-- Infinitely many consecutive pairs of powerful numbers, neither of which is a square. -/
theorem infinite_consecutive_powerful_nonsquare :
    {n : ℕ | Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨hpell, hX, hY, hle⟩ := sol_spec N
  set X := (sol N).1
  set Y := (sol N).2
  have hY0 : Y ≠ 0 := by omega
  have hX0 : X ≠ 0 := by
    rintro h0; rw [h0] at hpell; omega
  refine ⟨23 * Y ^ 2, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact powerful_prime_mul_sq (by norm_num) hY
  · rw [← hpell]; exact powerful_prime_mul_sq Nat.prime_two hX
  · exact not_isSquare_prime_mul_sq (by norm_num) hY0
  · rw [← hpell]; exact not_isSquare_prime_mul_sq Nat.prime_two hX0
  · have : Y ≤ Y ^ 2 := Nat.le_self_pow two_ne_zero Y
    omega

end Ascent

#print axioms Ascent.not_consecutive_powerful_imp_square
#print axioms Ascent.infinite_consecutive_powerful_nonsquare
