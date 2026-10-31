import Mathlib
import LeanProofs.MelfiCriterion

/-!
# An explicit weird-number region for 2^k·p·q (Erdős #470 partial)

AI-made by Ascent, Oct 28, 2026. Builds on `Melfi.weird_iff` (LeanProofs/MelfiCriterion.lean).
With `x = 2^(k+2)`, `p = x - a`, `q = x + b`, `a = b + 2j + 4`, the condition
`a² + a b < x + 2b + 2` forces `2^k p q` to be weird (abundant and not pseudoperfect).
This region contains the one in Melfi 2015 (J. Number Theory), Theorem 1 (`a < √(x/8)`),
whose points satisfy `a(a+b) < x/4`. It is a constant-factor widening of a conditional
route to infinitely many primitive weird numbers (it still needs primes in short intervals
near `2^(k+2)`), not a proof of Erdős #470. Primitivity is not formalized here.
-/

namespace Melfi

theorem noT (P b j T : ℕ) (hP : b + 2*j + 4 < 2*P)
    (h : (b+2*j+4)^2 + (b+2*j+4)*b < 2*P + 2*b + 2)
    (h1 : (2*P - (b+2*j+4)) * T ≤ P*(2*j+1) + (b+2*j+3)*(b+1))
    (h2 : P*(2*j+1) + (b+2*j+3)*(b+1) ≤ (2*P+b)*T + (P - 1)) : False := by
  obtain ⟨p, hp⟩ : ∃ p, 2*P = p + (b+2*j+4) := ⟨2*P - (b+2*j+4), by omega⟩
  have hp' : 2*P - (b+2*j+4) = p := by omega
  rw [hp'] at h1
  have hP1 : 1 ≤ P := by omega
  rcases Nat.lt_or_ge j T with hT | hT
  · have : p*(j+1) ≤ p*T := Nat.mul_le_mul_left _ hT
    nlinarith
  · have : (2*P+b)*T ≤ (2*P+b)*j := Nat.mul_le_mul_left _ hT
    have e : P - 1 + 1 = P := by omega
    nlinarith

open ArithmeticFunction in
theorem sum_properDivisors_eq {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ i ∈ Nat.properDivisors (2 ^ k * p * q), i + 2 ^ k * p * q
      = (2 ^ (k+1) - 1) * (p + 1) * (q + 1) := by
  rw [← Nat.sum_divisors_eq_sum_properDivisors_add_self, ← sigma_one_apply]
  have c1 : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have c2 : Nat.Coprime (2 ^ k * p) q := by
    refine Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩
    · exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
    · exact (Nat.coprime_primes hp hq).2 hpq
  rw [isMultiplicative_sigma.map_mul_of_coprime c2, isMultiplicative_sigma.map_mul_of_coprime c1,
    sigma_one_apply_prime_pow Nat.prime_two]
  have hp1 : sigma 1 p = p + 1 := by
    rw [sigma_one_apply, Nat.Prime.sum_divisors hp]
  have hq1 : sigma 1 q = q + 1 := by
    rw [sigma_one_apply, Nat.Prime.sum_divisors hq]
  rw [hp1, hq1]
  have geom : ∀ n, ∑ i ∈ Finset.range (n + 1), 2 ^ i = 2 ^ (n + 1) - 1 := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n+1) := Nat.one_le_two_pow
      rw [pow_succ 2 (n+1)]; omega
  rw [geom]

/-- **Wide region.** `2^k p q` is weird when `p = 2^(k+2) - a`, `q = 2^(k+2) + b` are primes,
`a = b + 2j + 4`, and `a² + a b < 2^(k+2) + 2b + 2`. -/
theorem weird_of_region {k p q b j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpdef : p + (b + 2*j + 4) = 2 ^ (k+2)) (hqdef : q = 2 ^ (k+2) + b)
    (h : (b+2*j+4)^2 + (b+2*j+4)*b < 2 ^ (k+2) + 2*b + 2) :
    Nat.Abundant (2 ^ k * p * q) ∧ ¬ Nat.Pseudoperfect (2 ^ k * p * q) := by
  obtain ⟨P, hPdef⟩ : ∃ P, 2 ^ (k+1) = P := ⟨_, rfl⟩
  have hx : 2 ^ (k+2) = 2 * P := by rw [← hPdef, pow_succ]; ring
  have hk : 2 * 2 ^ k = P := by rw [← hPdef, pow_succ]; ring
  rw [hx] at hpdef hqdef h
  have hP2 : 2 ≤ P := by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
  have hb : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    have hq' := hq
    rw [hqdef, hb0', Nat.add_zero] at hq'
    rcases hq'.eq_one_or_self_of_dvd 2 ⟨P, rfl⟩ with h' | h' <;> omega
  obtain ⟨a, ha⟩ : ∃ a, b + 2*j + 4 = a := ⟨_, rfl⟩
  rw [ha] at hpdef h
  have ha5 : 5 ≤ a := by omega
  have hab : b < a := by omega
  have haP : 2 * a + 2 ≤ P := by nlinarith
  have hq2 : q ≠ 2 := by omega
  have hp2 : p ≠ 2 := by intro h2; subst h2; nlinarith
  have hpq : p < q := by omega
  set A := P*(2*j+1) + (b+2*j+3)*(b+1) with hAdef
  have hsum : ∑ i ∈ Nat.properDivisors (2 ^ k * p * q), i = 2 ^ k * p * q + A := by
    have e := sum_properDivisors_eq (k := k) hp hq hp2 hq2 hpq.ne
    rw [hPdef] at e
    have hn : 2 ^ k * p * q * 2 = P * p * q := by rw [← hk]; ring
    -- (P-1)(p+1)(q+1) = 2·2^k p q + A
    have hn2 : 2 * (2 ^ k * p * q) = P * p * q := by rw [← hk]; ring
    have key : (P - 1) * (p + 1) * (q + 1) = 2 * (2 ^ k * p * q) + A := by
      rw [hn2]
      obtain ⟨P1, rfl⟩ : ∃ P1, P = P1 + 1 := ⟨P - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have hp' : (p:ℤ) = 2*(P1+1) - (b + 2*j + 4) := by
        have := congrArg (fun n : ℕ => (n:ℤ)) hpdef; push_cast at this; rw [← ha] at this; push_cast at this; linarith
      zify; rw [hqdef, hAdef, hp']; push_cast; ring
    omega
  have hApq : A < p * q := by nlinarith
  have hA : A < p * 2 ^ (k+1) := by rw [hPdef]; nlinarith
  have hd : q - p ≤ 2 ^ (k+1) := by rw [hPdef]; omega
  refine (weird_iff hp hq hp2 hq2 hpq hsum hApq hA hd).2 ⟨by positivity, ?_⟩
  rintro ⟨T, hT, h1, h2⟩
  rw [hPdef] at hT h2
  have hpa : p = 2*P - a := by omega
  rw [hpa] at h1
  subst ha
  exact noT P b j T (by omega) h h1 (by rw [hqdef] at h2; exact h2)

end Melfi

#print axioms Melfi.weird_of_region
