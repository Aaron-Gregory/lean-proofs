import Mathlib

/-!
# Melfi's exact criterion for weird numbers 2^k·p·q (Erdős #470 partial)

AI-made by Ascent, Oct 26, 2026. Proper divisors of n = 2^k p q (p < q odd primes) have subset sums
  s + p X + q Y + p q Z,  s, X, Y ≤ M = 2^(k+1) - 1, Z ≤ 2^k - 1,
and n is weird iff A = σ(n) - 2n > 0 is not such a sum. This file proves the arithmetic
core that turns "A is a subset sum" into "some integer T lies in an interval":
    with d = q - p ≤ M + 1 and A < p (M + 1),
  A = s + pX + (p+d)Y (s,X,Y ≤ M)  ↔  ∃ T ≤ M, p T ≤ A ≤ (p+d) T + M.
The main theorem `weird_iff` then links this to `Nat.properDivisors`, `Nat.Pseudoperfect`
and `Nat.Abundant`.
-/

namespace Melfi

/-- `A` is a sum `s + p X + q Y` with all three coefficients at most `M`. -/
def Rep (p q M A : ℕ) : Prop :=
  ∃ s X Y : ℕ, s ≤ M ∧ X ≤ M ∧ Y ≤ M ∧ A = s + p * X + q * Y

/-- `A` is a sum `s + p X + q Y + p q Z` with `s, X, Y ≤ M`, `Z ≤ N`. -/
def Rep4 (p q M N A : ℕ) : Prop :=
  ∃ s X Y Z : ℕ, s ≤ M ∧ X ≤ M ∧ Y ≤ M ∧ Z ≤ N ∧ A = s + p * X + q * Y + p * q * Z

/-- Below `p q` the `p q Z` term must vanish. -/
theorem rep4_iff_rep {p q M N A : ℕ} (hA : A < p * q) :
    Rep4 p q M N A ↔ Rep p q M A := by
  constructor
  · rintro ⟨s, X, Y, Z, hs, hX, hY, hZ, rfl⟩
    have hZ0 : Z = 0 := by
      by_contra h
      have : p * q ≤ p * q * Z := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
      omega
    subst hZ0
    exact ⟨s, X, Y, hs, hX, hY, by simp⟩
  · rintro ⟨s, X, Y, hs, hX, hY, rfl⟩
    exact ⟨s, X, Y, 0, hs, hX, hY, Nat.zero_le _, by simp⟩

/-- The exact criterion (core). -/
theorem rep_iff_interval {p d M A : ℕ} (hd : d ≤ M + 1) (hA : A < p * (M + 1)) :
    Rep p (p + d) M A ↔ ∃ T : ℕ, T ≤ M ∧ p * T ≤ A ∧ A ≤ (p + d) * T + M := by
  constructor
  · rintro ⟨s, X, Y, hs, hX, hY, rfl⟩
    refine ⟨X + Y, ?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      have h1 : p * (M + 1) ≤ p * (X + Y) := Nat.mul_le_mul_left _ h
      have h2 : p * (X + Y) ≤ s + p * X + (p + d) * Y := by nlinarith
      omega
    · nlinarith
    · nlinarith
  · rintro ⟨T, hT, h1, h2⟩
    -- r = A - pT ∈ [0, dT + M]; write r = d Y + s with Y ≤ T, s ≤ M.
    obtain ⟨r, rfl⟩ : ∃ r, A = p * T + r := ⟨A - p * T, by omega⟩
    have hr : r ≤ d * T + M := by nlinarith
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      refine ⟨r, T, 0, by simpa using hr, hT, Nat.zero_le _, by ring⟩
    · by_cases hc : r / d ≤ T
      · refine ⟨r % d, T - r / d, r / d, ?_, le_trans (Nat.sub_le _ _) hT, le_trans hc hT, ?_⟩
        · have := Nat.mod_lt r hdpos; omega
        · have hdiv := Nat.div_add_mod r d
          have : p * T = p * (T - r / d) + p * (r / d) := by
            rw [← Nat.mul_add]; congr 1; omega
          nlinarith
      · push Not at hc
        have hdT : d * T ≤ r := by
          have := (Nat.le_div_iff_mul_le hdpos).1 hc.le
          linarith [Nat.mul_comm T d]
        refine ⟨r - d * T, 0, T, by omega, Nat.zero_le _, hT, ?_⟩
        have e : (p + d) * T = p * T + d * T := by ring
        rw [e]; omega

/-- Brute-force decidable version of `Rep`, for cross-checking. -/
def repB (p q M A : ℕ) : Bool :=
  (List.range (M + 1)).any fun s => (List.range (M + 1)).any fun X =>
    (List.range (M + 1)).any fun Y => A == s + p * X + q * Y

def critB (p q M A : ℕ) : Bool :=
  (List.range (M + 1)).any fun T => p * T ≤ A && A ≤ q * T + M

-- Sanity: k = 2 (M = 7), p = 13, q = 19 (d = 6), all A < p (M+1) = 104.
example : (List.range 104).all (fun A => repB 13 19 7 A == critB 13 19 7 A) = true := by
  decide

open Finset

/-- `N` is a subset sum of `S`. -/
def SS (S : Finset ℕ) (N : ℕ) : Prop := ∃ s ⊆ S, ∑ i ∈ s, i = N

theorem ss_union {A B : Finset ℕ} (h : Disjoint A B) (N : ℕ) :
    SS (A ∪ B) N ↔ ∃ x y, SS A x ∧ SS B y ∧ N = x + y := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨∑ i ∈ s ∩ A, i, ∑ i ∈ s ∩ B, i, ⟨_, inter_subset_right, rfl⟩,
      ⟨_, inter_subset_right, rfl⟩, ?_⟩
    rw [← sum_union (h.mono inter_subset_right inter_subset_right),
      ← inter_union_distrib_left, inter_eq_left.mpr hs]
  · rintro ⟨x, y, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u ∪ v, union_subset_union hu hv, sum_union (h.mono hu hv)⟩

theorem ss_image_mul {c : ℕ} (hc : 0 < c) (B : Finset ℕ) (N : ℕ) :
    SS (B.image (c * ·)) N ↔ ∃ x, SS B x ∧ N = c * x := by
  have inj : ∀ a ∈ (B : Set ℕ), ∀ b ∈ (B : Set ℕ), c * a = c * b → a = b :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hc h
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := subset_image_iff.mp hs
    refine ⟨∑ i ∈ u, i, ⟨u, hu, rfl⟩, ?_⟩
    rw [sum_image (fun a ha b hb h => Nat.eq_of_mul_eq_mul_left hc h), mul_sum]
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u.image (c * ·), image_subset_image hu, ?_⟩
    rw [sum_image (fun a ha b hb h => Nat.eq_of_mul_eq_mul_left hc h), mul_sum]

/-- Powers `2^i`, `i < m`. -/
def B (m : ℕ) : Finset ℕ := (range m).image (2 ^ ·)

theorem ss_B (m N : ℕ) : SS (B m) N ↔ N < 2 ^ m := by
  have inj : ∀ a b : ℕ, 2 ^ a = 2 ^ b → a = b := fun a b h => Nat.pow_right_injective le_rfl h
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := subset_image_iff.mp hs
    rw [sum_image (fun a _ b _ h => inj a b h)]
    exact Nat.geomSum_lt le_rfl (fun k hk => mem_range.mp (hu hk))
  · intro hN
    refine ⟨N.bitIndices.toFinset.image (2 ^ ·), image_subset_image ?_, ?_⟩
    · intro a ha
      have h1 := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp ha)
      exact mem_range.mpr ((Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 hN))
    · rw [sum_image (fun a _ b _ h => inj a b h)]
      simp

theorem ss_cB {c : ℕ} (hc : 0 < c) (m N : ℕ) :
    SS ((B m).image (c * ·)) N ↔ ∃ x, x < 2 ^ m ∧ N = c * x := by
  rw [ss_image_mul hc]; simp only [ss_B]


def R (k p q : ℕ) : Finset ℕ :=
  B (k + 1) ∪ (B (k + 1)).image (p * ·) ∪ (B (k + 1)).image (q * ·) ∪ (B k).image (p * q * ·)

theorem divisors_eq {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Nat.divisors (2 ^ k * p * q) = insert (2 ^ k * p * q) (R k p q) := by
  ext d
  rw [Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_prime_pow Nat.prime_two, hp.divisors,
    hq.divisors]
  simp only [mem_mul, R, B, mem_insert, mem_union, mem_image, mem_range, mem_map,
    Function.Embedding.coeFn_mk, mem_singleton]
  constructor
  · rintro ⟨x, ⟨y, ⟨i, hi, rfl⟩, z, rfl | rfl, rfl⟩, w, rfl | rfl, rfl⟩
    · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨i, hi, by ring⟩)))
    · exact Or.inr (Or.inl (Or.inr ⟨2 ^ i, ⟨i, hi, rfl⟩, by ring⟩))
    · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨2 ^ i, ⟨i, hi, rfl⟩, by ring⟩)))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact Or.inr (Or.inr ⟨2 ^ i, ⟨i, h, rfl⟩, by ring⟩)
      · exact Or.inl rfl
  · rintro (rfl | (((⟨i, hi, rfl⟩ | ⟨_, ⟨i, hi, rfl⟩, rfl⟩) | ⟨_, ⟨i, hi, rfl⟩, rfl⟩) |
      ⟨_, ⟨i, hi, rfl⟩, rfl⟩))
    · exact ⟨2 ^ k * p, ⟨2 ^ k, ⟨k, by omega, rfl⟩, p, Or.inr rfl, rfl⟩, q, Or.inr rfl, rfl⟩
    · exact ⟨2 ^ i, ⟨2 ^ i, ⟨i, hi, rfl⟩, 1, Or.inl rfl, by ring⟩, 1, Or.inl rfl, by ring⟩
    · exact ⟨2 ^ i * p, ⟨2 ^ i, ⟨i, hi, rfl⟩, p, Or.inr rfl, rfl⟩, 1, Or.inl rfl, by ring⟩
    · exact ⟨2 ^ i, ⟨2 ^ i, ⟨i, hi, rfl⟩, 1, Or.inl rfl, by ring⟩, q, Or.inr rfl, by ring⟩
    · exact ⟨2 ^ i * p, ⟨2 ^ i, ⟨i, by omega, rfl⟩, p, Or.inr rfl, rfl⟩, q, Or.inr rfl, by ring⟩


theorem not_dvd_two_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (i : ℕ) : ¬ r ∣ 2 ^ i :=
  fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))

theorem not_dvd_mul_two_pow {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hr2 : r ≠ 2) (hrs : r ≠ s)
    (i : ℕ) : ¬ r ∣ s * 2 ^ i := fun h =>
  (hr.dvd_mul.mp h).elim (fun h => hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp h))
    (not_dvd_two_pow hr hr2 i)

section
variable {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
include hp hq hp2 hq2 hpq

theorem disj1 : Disjoint (B (k + 1)) ((B (k + 1)).image (p * ·)) := by
  simp only [B, disjoint_left, mem_image, mem_range]
  rintro _ ⟨i, -, rfl⟩ ⟨_, ⟨j, -, rfl⟩, h⟩
  exact not_dvd_two_pow hp hp2 i ⟨2 ^ j, h.symm⟩

theorem disj2 : Disjoint (B (k + 1) ∪ (B (k + 1)).image (p * ·)) ((B (k + 1)).image (q * ·)) := by
  simp only [B, disjoint_left, mem_union, mem_image, mem_range]
  rintro _ (⟨i, -, rfl⟩ | ⟨_, ⟨i, -, rfl⟩, rfl⟩) ⟨_, ⟨j, -, rfl⟩, h⟩
  · exact not_dvd_two_pow hq hq2 i ⟨2 ^ j, h.symm⟩
  · exact not_dvd_mul_two_pow hq hp hq2 (Ne.symm hpq) i ⟨2 ^ j, h.symm⟩

theorem disj3 : Disjoint (B (k + 1) ∪ (B (k + 1)).image (p * ·) ∪ (B (k + 1)).image (q * ·))
    ((B k).image (p * q * ·)) := by
  simp only [B, disjoint_left, mem_union, mem_image, mem_range]
  rintro _ ((⟨i, -, rfl⟩ | ⟨_, ⟨i, -, rfl⟩, rfl⟩) | ⟨_, ⟨i, -, rfl⟩, rfl⟩) ⟨_, ⟨j, -, rfl⟩, h⟩
  · exact not_dvd_two_pow hq hq2 i ⟨p * 2 ^ j, by rw [← h]; ring⟩
  · exact not_dvd_mul_two_pow hq hp hq2 (Ne.symm hpq) i ⟨p * 2 ^ j, by rw [← h]; ring⟩
  · exact not_dvd_mul_two_pow hp hq hp2 hpq i ⟨q * 2 ^ j, by rw [← h]; ring⟩

theorem not_mem_R : 2 ^ k * p * q ∉ R k p q := by
  have p2 := hp.two_le
  have q2 := hq.two_le
  simp only [R, B, mem_union, mem_image, mem_range]
  rintro (((⟨i, hi, h⟩ | ⟨_, ⟨i, hi, rfl⟩, h⟩) | ⟨_, ⟨i, hi, rfl⟩, h⟩) | ⟨_, ⟨i, hi, rfl⟩, h⟩)
  all_goals
    have hle : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk : 0 < 2 ^ k := by positivity
  · have h1 : 2 ^ k * 4 ≤ 2 ^ k * (p * q) := Nat.mul_le_mul_left _ (by nlinarith)
    have e : 2 ^ k * p * q = 2 ^ k * (p * q) := by ring
    linarith
  · have h1 : p * 2 ^ i ≤ p * 2 ^ k := Nat.mul_le_mul_left _ hle
    have h2 : p * 2 ^ k * 2 ≤ p * 2 ^ k * q := Nat.mul_le_mul_left _ q2
    have h3 : 0 < p * 2 ^ k := by positivity
    have e : 2 ^ k * p * q = p * 2 ^ k * q := by ring
    linarith
  · have h1 : q * 2 ^ i ≤ q * 2 ^ k := Nat.mul_le_mul_left _ hle
    have h2 : q * 2 ^ k * 2 ≤ q * 2 ^ k * p := Nat.mul_le_mul_left _ p2
    have h3 : 0 < q * 2 ^ k := by positivity
    have e : 2 ^ k * p * q = q * 2 ^ k * p := by ring
    linarith
  · have hlt : 2 ^ i < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hi
    have : p * q * 2 ^ i < p * q * 2 ^ k := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    have e : 2 ^ k * p * q = p * q * 2 ^ k := by ring
    linarith

theorem properDivisors_eq : Nat.properDivisors (2 ^ k * p * q) = R k p q := by
  have hn : 2 ^ k * p * q ≠ 0 := by
    have := hp.pos; have := hq.pos; positivity
  have h := Nat.insert_self_properDivisors hn
  rw [divisors_eq hp hq] at h
  rw [← erase_insert (Nat.self_notMem_properDivisors (n := 2 ^ k * p * q)), h,
    erase_insert (not_mem_R hp hq hp2 hq2 hpq)]

theorem ss_R (A : ℕ) : SS (R k p q) A ↔ ∃ s X Y Z, s < 2 ^ (k + 1) ∧ X < 2 ^ (k + 1) ∧
    Y < 2 ^ (k + 1) ∧ Z < 2 ^ k ∧ A = s + p * X + q * Y + p * q * Z := by
  have pp := hp.pos; have qp := hq.pos
  rw [R, ss_union (disj3 hp hq hp2 hq2 hpq)]
  simp only [ss_union (disj2 hp hq hp2 hq2 hpq), ss_union (disj1 hp hq hp2 hq2 hpq), ss_B,
    ss_cB pp, ss_cB qp, ss_cB (Nat.mul_pos pp qp)]
  constructor
  · rintro ⟨_, _, ⟨_, _, ⟨s, _, hs, ⟨X, hX, rfl⟩, rfl⟩, ⟨Y, hY, rfl⟩, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨s, X, Y, Z, hs, hX, hY, hZ, rfl⟩
  · rintro ⟨s, X, Y, Z, hs, hX, hY, hZ, rfl⟩
    exact ⟨_, _, ⟨_, _, ⟨s, _, hs, ⟨X, hX, rfl⟩, rfl⟩, ⟨Y, hY, rfl⟩, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
end

theorem ss_compl {S : Finset ℕ} {N A : ℕ} (h : ∑ i ∈ S, i = N + A) : SS S N ↔ SS S A := by
  constructor
  · rintro ⟨s, hs, hsum⟩
    refine ⟨S \ s, sdiff_subset, ?_⟩
    have := sum_sdiff (f := fun i => i) hs
    omega
  · rintro ⟨s, hs, hsum⟩
    refine ⟨S \ s, sdiff_subset, ?_⟩
    have := sum_sdiff (f := fun i => i) hs
    omega


/-- **Melfi's exact criterion, formal version.** For `n = 2^k p q` with `p < q` odd primes,
`A = σ(n) - 2n` (given via `hsum`), `A < p q`, `A < p·2^(k+1)` and `q - p ≤ 2^(k+1)`:
`n` is pseudoperfect iff some integer `T < 2^(k+1)` has `p T ≤ A ≤ q T + 2^(k+1) - 1`. -/
theorem pseudoperfect_iff {k p q A : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p < q)
    (hsum : ∑ i ∈ Nat.properDivisors (2 ^ k * p * q), i = 2 ^ k * p * q + A)
    (hApq : A < p * q) (hA : A < p * 2 ^ (k + 1)) (hd : q - p ≤ 2 ^ (k + 1)) :
    Nat.Pseudoperfect (2 ^ k * p * q) ↔
      ∃ T, T < 2 ^ (k + 1) ∧ p * T ≤ A ∧ A ≤ q * T + (2 ^ (k + 1) - 1) := by
  have hpne : p ≠ q := hpq.ne
  have h2 : 0 < 2 ^ (k + 1) := by positivity
  have h2' : 0 < 2 ^ k := by positivity
  have hn : 0 < 2 ^ k * p * q := by have := hp.pos; have := hq.pos; positivity
  have step1 : Nat.Pseudoperfect (2 ^ k * p * q) ↔ SS (R k p q) A := by
    rw [← properDivisors_eq hp hq hp2 hq2 hpne, ← ss_compl hsum]
    exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
  have step2 : SS (R k p q) A ↔ Rep4 p q (2 ^ (k + 1) - 1) (2 ^ k - 1) A := by
    rw [ss_R hp hq hp2 hq2 hpne]
    constructor
    · rintro ⟨s, X, Y, Z, hs, hX, hY, hZ, h⟩
      exact ⟨s, X, Y, Z, by omega, by omega, by omega, by omega, h⟩
    · rintro ⟨s, X, Y, Z, hs, hX, hY, hZ, h⟩
      exact ⟨s, X, Y, Z, by omega, by omega, by omega, by omega, h⟩
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hM : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by omega
  rw [step1, step2, rep4_iff_rep hApq,
    rep_iff_interval (by omega) (by rw [hM]; exact hA)]
  constructor
  · rintro ⟨T, hT, h1, h2⟩; exact ⟨T, by omega, h1, h2⟩
  · rintro ⟨T, hT, h1, h2⟩; exact ⟨T, by omega, h1, h2⟩

/-- Weird = abundant and not pseudoperfect. -/
theorem weird_iff {k p q A : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p < q)
    (hsum : ∑ i ∈ Nat.properDivisors (2 ^ k * p * q), i = 2 ^ k * p * q + A)
    (hApq : A < p * q) (hA : A < p * 2 ^ (k + 1)) (hd : q - p ≤ 2 ^ (k + 1)) :
    (Nat.Abundant (2 ^ k * p * q) ∧ ¬ Nat.Pseudoperfect (2 ^ k * p * q)) ↔
      (0 < A ∧ ¬ ∃ T, T < 2 ^ (k + 1) ∧ p * T ≤ A ∧ A ≤ q * T + (2 ^ (k + 1) - 1)) := by
  rw [pseudoperfect_iff hp hq hp2 hq2 hpq hsum hApq hA hd, Nat.Abundant, hsum]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-- Same as `weird_iff`, using Mathlib's `Nat.Weird` (`Abundant ∧ ¬ Pseudoperfect`). -/
theorem weird_iff' {k p q A : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p < q)
    (hsum : ∑ i ∈ Nat.properDivisors (2 ^ k * p * q), i = 2 ^ k * p * q + A)
    (hApq : A < p * q) (hA : A < p * 2 ^ (k + 1)) (hd : q - p ≤ 2 ^ (k + 1)) :
    Nat.Weird (2 ^ k * p * q) ↔
      (0 < A ∧ ¬ ∃ T, T < 2 ^ (k + 1) ∧ p * T ≤ A ∧ A ≤ q * T + (2 ^ (k + 1) - 1)) :=
  weird_iff hp hq hp2 hq2 hpq hsum hApq hA hd

/-- 70 = 2·5·7, the smallest weird number, via the criterion (no `T` exists). -/
example : Nat.Abundant (2 ^ 1 * 5 * 7) ∧ ¬ Nat.Pseudoperfect (2 ^ 1 * 5 * 7) :=
  (weird_iff (A := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by norm_num)).2
    ⟨by norm_num, by rintro ⟨T, hT, h1, h2⟩; interval_cases T <;> omega⟩

/-- 572 = 2^2·11·13 is pseudoperfect: `T = 2` works. -/
example : Nat.Pseudoperfect (2 ^ 2 * 11 * 13) :=
  (pseudoperfect_iff (A := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)).2
    ⟨2, by norm_num, by norm_num, by norm_num⟩

end Melfi

#print axioms Melfi.rep_iff_interval
#print axioms Melfi.pseudoperfect_iff
#print axioms Melfi.weird_iff
#print axioms Melfi.weird_iff'
