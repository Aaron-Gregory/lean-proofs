import Mathlib

/-!
# IMO 2026 Problem 6: first reduction step (partial progress, NOT a full solution)

Sequence `a 0, a 1, ...` (0-indexed), each term > 1, and `a (n+1)` is the least
integer above `a n` sharing a common factor with all of `a 0, ..., a n`.

Proved here:
* `pairwise`: every two terms share a common factor.
* `mem_range_iff`: the set of terms is exactly `{m ≥ a 0 | ∀ i, 1 < gcd m (a i)}`.
  So the sequence is the increasing enumeration of a set defined by a single
  self-referential coprimality condition, and periodicity reduces to showing
  that this condition depends on only finitely many radicals.
-/

namespace Ascent.IMO2026P6

structure Greedy (a : ℕ → ℕ) : Prop where
  gt_one : ∀ n, 1 < a n
  lt_succ : ∀ n, a n < a (n + 1)
  shares : ∀ n, ∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)
  least : ∀ n m, a n < m → m < a (n + 1) → ∃ i ≤ n, Nat.gcd m (a i) = 1

variable {a : ℕ → ℕ}

theorem strictMono (h : Greedy a) : StrictMono a :=
  strictMono_nat_of_lt_succ h.lt_succ

theorem pairwise (h : Greedy a) (i j : ℕ) : 1 < Nat.gcd (a i) (a j) := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [Nat.gcd_comm]; exact h.shares n i (by omega)
  · rw [Nat.gcd_self]; exact h.gt_one i
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact h.shares n j (by omega)

theorem mem_range_iff (h : Greedy a) (m : ℕ) (hm : a 0 ≤ m) :
    (∃ n, a n = m) ↔ ∀ i, 1 < Nat.gcd m (a i) := by
  constructor
  · rintro ⟨n, rfl⟩ i; exact pairwise h n i
  · intro hall
    have hex : ∃ k, m < a k := ⟨m + 1, by
      have : m + 1 ≤ a (m + 1) := (strictMono h).id_le (m + 1)
      omega⟩
    classical
    let k := Nat.find hex
    have hk : m < a k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0; have : m < a 0 := h0 ▸ hk; omega
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hle : ¬ m < a n := Nat.find_min hex (by omega)
    rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
    · exact ⟨n, heq⟩
    · exfalso
      obtain ⟨i, -, hi⟩ := h.least n m hlt (hn ▸ hk)
      have := hall i; omega


/-- Hypothesis `SmallShared B`: every two terms share a prime factor `≤ B`.
(Empirically true with `B = a 0` for all `a 0 < 400`; NOT proved here.) -/
def SmallShared (a : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ i j, ∃ p, p.Prime ∧ p ≤ B ∧ p ∣ a i ∧ p ∣ a j

lemma prime_dvd_fact {p B : ℕ} (hp : p.Prime) (hpB : p ≤ B) : p ∣ B.factorial :=
  Nat.dvd_factorial hp.pos hpB

lemma one_lt_gcd_of_dvd {p x y : ℕ} (hp : p.Prime) (hx : p ∣ x) (hy : p ∣ y)
    (hy0 : 0 < y) : 1 < Nat.gcd x y :=
  lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right x hy0) (Nat.dvd_gcd hx hy))

/-- Under `SmallShared`, the set of terms is `B!`-periodic above `a 0`. -/
theorem range_periodic (h : Greedy a) {B : ℕ} (hS : SmallShared a B) (m : ℕ)
    (hm : a 0 ≤ m) :
    (∃ n, a n = m) ↔ (∃ n, a n = m + B.factorial) := by
  rw [mem_range_iff h m hm, mem_range_iff h _ (by omega)]
  constructor
  · intro hall i
    obtain ⟨n, hn⟩ := (mem_range_iff h m hm).mpr hall
    obtain ⟨p, hp, hpB, hpm, hpi⟩ := hS n i
    rw [hn] at hpm
    exact one_lt_gcd_of_dvd hp (dvd_add hpm (prime_dvd_fact hp hpB)) hpi (by have := h.gt_one i; omega)
  · intro hall i
    obtain ⟨n, hn⟩ := (mem_range_iff h _ (by omega)).mpr hall
    obtain ⟨p, hp, hpB, hpm, hpi⟩ := hS n i
    rw [hn] at hpm
    have : p ∣ m := (Nat.dvd_add_right (prime_dvd_fact hp hpB)).mp (by
      rwa [add_comm] at hpm)
    exact one_lt_gcd_of_dvd hp this hpi (by have := h.gt_one i; omega)

/-- Conditional IMO 2026 P6: if every two terms share a prime `≤ B`, the sequence is
periodic in the strong sense `a (n + T) = a n + B!` for all `n`. -/
theorem periodic_of_smallShared (h : Greedy a) {B : ℕ} (hS : SmallShared a B) :
    ∃ T > 0, ∀ n, a (n + T) = a n + B.factorial := by
  have hM : 0 < B.factorial := Nat.factorial_pos B
  have hmono := strictMono h
  obtain ⟨T, hT⟩ := (range_periodic h hS (a 0) le_rfl).mp ⟨0, rfl⟩
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; omega
    · exact h0
  refine ⟨T, hTpos, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
    have ha0n : a 0 ≤ a (n + 1) := hmono.monotone (Nat.zero_le _)
    apply le_antisymm
    · -- a (n+1) + M is a term, above a (n + T), so at least a (n+1+T)
      obtain ⟨k, hk⟩ := (range_periodic h hS (a (n + 1)) ha0n).mp ⟨n + 1, rfl⟩
      have h1 : a (n + T) < a k := by
        rw [ih, hk]; have : a n < a (n + 1) := hmono (show n < n + 1 by omega); omega
      have h2 : n + T < k := hmono.lt_iff_lt.mp h1
      have h3 : a (n + 1 + T) ≤ a k :=
        hmono.monotone (by omega)
      omega
    · -- a (n+1+T) - M is a term, above a n, so at least a (n+1)
      have hgt : a (n + T) < a (n + 1 + T) := hmono (by omega)
      have hge : a 0 + B.factorial ≤ a (n + T) := by
        rw [ih]; have := hmono.monotone (Nat.zero_le n); omega
      set m := a (n + 1 + T) - B.factorial with hmdef
      have hmM : m + B.factorial = a (n + 1 + T) := by omega
      obtain ⟨k, hk⟩ := (range_periodic h hS m (by omega)).mpr ⟨n + 1 + T, hmM.symm⟩
      have h1 : a n < a k := by rw [hk]; omega
      have h2 : n < k := hmono.lt_iff_lt.mp h1
      have h3 : a (n + 1) ≤ a k := hmono.monotone (by omega)
      omega

end Ascent.IMO2026P6

#print axioms Ascent.IMO2026P6.mem_range_iff
#print axioms Ascent.IMO2026P6.periodic_of_smallShared
