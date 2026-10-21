import Mathlib

/-!
# IMO 2026 Problem 5 (Ascent, G3c)

Determine all `f : ℝ>0 → ℝ>0` with
  √((x² + f(y)²)/2) ≥ (f(x) + y)/2 ≥ √(x f(y))   for all x, y > 0.
Answer: exactly `f x = x + c` with a constant `c ≥ 0`.

Modelling: `f : ℝ → ℝ`, required positive on positives; only values on
positives matter, and the conclusion is stated on positives only.

Proof sketch (found by Ascent, Oct 20 2026, before seeing any solution):
1. Put x = f(y) in both inequalities: f(f y) = 2 f y - y.
2. So f^[n] y = y + n (f y - y); positivity of iterates forces d(y) := f y - y ≥ 0.
3. Put x = f a (a orbit point), y = b: (d b - d a)(f a + f b) ≤ (f a - f b)²
   when d a < d b. Matching two arithmetic progressions far out kills any
   difference between two positive values of d.
4. So d takes values in {0, c}. Inequality (I) separates the two level sets:
   2c(x+y) + c² ≤ (x-y)². A march to the right from any point then shows
   d is constant on [w, ∞) for every w, so both level sets can't coexist.
-/

namespace Ascent.IMO2026P5

open Real

/-- The IMO 2026 Problem 5 condition. -/
def Good (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → 0 < f x) ∧
  ∀ x y, 0 < x → 0 < y →
    (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧ √(x * f y) ≤ (f x + y) / 2

theorem good_of_shift (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : ∀ x, 0 < x → f x = x + c) : Good f := by
  refine ⟨fun x hx => by rw [hf x hx]; linarith, fun x y hx hy => ?_⟩
  rw [hf x hx, hf y hy]
  constructor
  · refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    nlinarith [sq_nonneg (x - (y + c))]
  · rw [show (x + c + y) / 2 = √(((x + c + y) / 2) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (x - (y + c))]

theorem shift_of_good (f : ℝ → ℝ) (hf : Good f) :
    ∃ c, 0 ≤ c ∧ ∀ x, 0 < x → f x = x + c := by
  obtain ⟨hpos, hineq⟩ := hf
  -- squared forms of the two inequalities
  have h1 : ∀ x y, 0 < x → 0 < y → (f x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * f y ^ 2 := by
    intro x y hx hy
    have hle := (hineq x y hx hy).1
    have ht : 0 ≤ (f x + y) / 2 := by have := hpos x hx; linarith
    have hs : 0 ≤ (x ^ 2 + f y ^ 2) / 2 := by positivity
    have hsq := Real.sq_sqrt hs
    have := mul_self_le_mul_self ht hle
    nlinarith
  have h2 : ∀ x y, 0 < x → 0 < y → 4 * x * f y ≤ (f x + y) ^ 2 := by
    intro x y hx hy
    have hle := (hineq x y hx hy).2
    have hs : 0 ≤ x * f y := (mul_pos hx (hpos y hy)).le
    have hsq := Real.sq_sqrt hs
    have := mul_self_le_mul_self (Real.sqrt_nonneg _) hle
    nlinarith
  -- step 1: f (f y) = 2 f y - y
  have hff : ∀ y, 0 < y → f (f y) = 2 * f y - y := by
    intro y hy
    have hfy := hpos y hy
    have hffy := hpos (f y) hfy
    have a := h1 (f y) y hfy hy
    have b := h2 (f y) y hfy hy
    have : (f (f y) + y - 2 * f y) * (f (f y) + y + 2 * f y) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  -- step 2: iterates form an arithmetic progression
  have hiter_pos : ∀ y, 0 < y → ∀ n : ℕ, 0 < f^[n] y := by
    intro y hy n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [Function.iterate_succ_apply']; exact hpos _ ih
  have hiter : ∀ y, 0 < y → ∀ n : ℕ,
      f^[n] y = y + n * (f y - y) ∧ f^[n + 1] y = y + (n + 1) * (f y - y) := by
    intro y hy n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ n ih =>
      refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
      have e : f^[n + 1 + 1] y = f (f (f^[n] y)) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [e, hff _ (hiter_pos y hy n), ← Function.iterate_succ_apply' f n y, ih.2, ih.1]
      push_cast; ring
  have hd : ∀ y, 0 < y → y ≤ f y := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have hgap : 0 < y - f y := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (y / (y - f y))
    rw [div_lt_iff₀ hgap] at hn
    have h := (hiter y hy n).1
    have hp := hiter_pos y hy n
    have : (n : ℝ) * (f y - y) = -((n : ℝ) * (y - f y)) := by ring
    linarith
  -- step 3: two positive values of d coincide
  have hB : ∀ a b, 0 < a → 0 < b → 0 < f a - a → f a - a < f b - b → False := by
    intro a b ha hb hα hαβ
    obtain ⟨α, hαd⟩ : ∃ α, f a - a = α := ⟨_, rfl⟩
    obtain ⟨β, hβd⟩ : ∃ β, f b - b = β := ⟨_, rfl⟩
    rw [hαd] at hα hαβ
    rw [hβd] at hαβ
    have hβ : 0 < β := by linarith
    obtain ⟨e, hed⟩ : ∃ e, β - α = e := ⟨_, rfl⟩
    have hepos : 0 < e := by linarith
    have key : ∀ k j : ℕ, e * ((a + (k + 1) * α) + (b + (j + 1) * β)) ≤
        ((a + (k + 1) * α) - (b + (j + 1) * β)) ^ 2 := by
      intro k j
      have hx := hiter_pos a ha k
      have hy := hiter_pos b hb j
      have hfx : f (f^[k] a) = a + (k + 1) * α := by
        rw [← Function.iterate_succ_apply' f k a, ← hαd]; exact (hiter a ha k).2
      have hx' : f^[k] a = a + k * α := by rw [← hαd]; exact (hiter a ha k).1
      have hfy : f (f^[j] b) = b + (j + 1) * β := by
        rw [← Function.iterate_succ_apply' f j b, ← hβd]; exact (hiter b hb j).2
      have hy' : f^[j] b = b + j * β := by rw [← hβd]; exact (hiter b hb j).1
      have hfxpos := hpos _ hx
      have hffx := hff _ hx
      have hffxpos := hpos _ hfxpos
      have h := h2 (f (f^[k] a)) (f^[j] b) hfxpos hy
      have hS : 0 < f (f (f^[k] a)) + f^[j] b := by linarith
      rw [hffx, hfx, hfy, hx', hy'] at h
      rw [hffx, hfx, hx', hy'] at hS
      have hsum : 2 * (a + (k + 1) * α) - (a + k * α) + (b + j * β) =
          (a + (k + 1) * α) + (b + (j + 1) * β) - e := by rw [← hed]; ring
      rw [hsum] at h hS
      nlinarith [mul_pos hepos hS]
    obtain ⟨k, hk⟩ := exists_nat_gt ((β ^ 2 / e + b + β) / α)
    rw [div_lt_iff₀ hα] at hk
    have hA : β ^ 2 / e + b + β < a + (k + 1) * α := by nlinarith
    have hAb : 0 ≤ (a + (k + 1) * α - b) / β := by
      apply div_nonneg _ hβ.le
      have : 0 ≤ β ^ 2 / e := by positivity
      linarith
    have hj1 := Nat.floor_le hAb
    have hj2 := Nat.lt_floor_add_one ((a + (k + 1) * α - b) / β)
    rw [le_div_iff₀ hβ] at hj1
    rw [div_lt_iff₀ hβ] at hj2
    have hkey := key k ⌊(a + (k + 1) * α - b) / β⌋₊
    have hβe : e * (β ^ 2 / e) = β ^ 2 := by field_simp
    have hAe : β ^ 2 < e * (a + (k + 1) * α) := by
      have := mul_lt_mul_of_pos_left (show β ^ 2 / e < a + (k + 1) * α by
        have : 0 ≤ b + β := by linarith
        linarith) hepos
      linarith
    set j : ℕ := ⌊(a + (k + 1) * α - b) / β⌋₊
    have hd1 : 0 < b + (j + 1) * β - (a + (k + 1) * α) := by linarith
    have hd2 : b + (j + 1) * β - (a + (k + 1) * α) ≤ β := by linarith
    have hsq : ((a + (k + 1) * α) - (b + (j + 1) * β)) ^ 2 ≤ β ^ 2 := by nlinarith
    have hBpos : 0 < b + (j + 1) * β := by
      have := mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hβ.le
      linarith
    nlinarith [mul_pos hepos hBpos]
  -- step 4: d takes values in {0, c}, and the level sets are separated
  by_cases hall : ∀ x, 0 < x → f x - x = 0
  · exact ⟨0, le_refl _, fun x hx => by linarith [hall x hx]⟩
  push Not at hall
  obtain ⟨p, hp, hpne⟩ := hall
  obtain ⟨c, hc⟩ : ∃ c, f p - p = c := ⟨_, rfl⟩
  have hdp : 0 < c := by
    rw [← hc]; exact lt_of_le_of_ne (by linarith [hd p hp]) (Ne.symm hpne)
  refine ⟨c, hdp.le, ?_⟩
  have hposeq : ∀ x, 0 < x → 0 < f x - x → f x - x = c := by
    intro x hx hdx
    rcases lt_trichotomy (f x - x) c with h | h | h
    · exact (hB x p hx hp hdx (hc ▸ h)).elim
    · exact h
    · exact (hB p x hp hx (hc ▸ hdp) (hc ▸ h)).elim
  have hval : ∀ x, 0 < x → f x - x = 0 ∨ f x - x = c := by
    intro x hx
    rcases eq_or_lt_of_le (sub_nonneg.2 (hd x hx)) with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hposeq x hx h)
  have hsep : ∀ x y, 0 < x → 0 < y → f x - x = c → f y - y = 0 →
      2 * c * (x + y) + c ^ 2 ≤ (x - y) ^ 2 := by
    intro x y hx hy hxc hy0
    have := h1 x y hx hy
    have e1 : f x = x + c := by linarith
    have e2 : f y = y := by linarith
    rw [e1, e2] at this
    nlinarith
  have hmarch : ∀ w, 0 < w → ∀ t, w ≤ t → f t - t = f w - w := by
    intro w hw
    have hδ : 0 < min w c / 2 := half_pos (lt_min hw hdp)
    obtain ⟨δ, hδd⟩ : ∃ δ, min w c / 2 = δ := ⟨_, rfl⟩
    rw [hδd] at hδ
    have hδw : δ ≤ w / 2 := by rw [← hδd]; linarith [min_le_left w c]
    have hδc : δ ≤ c / 2 := by rw [← hδd]; linarith [min_le_right w c]
    have hδ2 : δ ^ 2 ≤ w * c / 4 := by
      nlinarith [mul_le_mul hδw hδc hδ.le (by linarith : (0 : ℝ) ≤ w / 2)]
    have claim : ∀ k : ℕ, ∀ t, w ≤ t → t ≤ w + k * δ → f t - t = f w - w := by
      intro k
      induction k with
      | zero =>
        intro t ht1 ht2
        have : t = w := by simp at ht2; linarith
        rw [this]
      | succ k ih =>
        intro t ht1 ht2
        push_cast at ht2
        have hkδ : 0 ≤ (k : ℝ) * δ := by positivity
        have ht'1 : w ≤ max w (t - δ) := le_max_left _ _
        have ht'2 : max w (t - δ) ≤ w + k * δ := max_le (by linarith) (by linarith)
        have ht'3 : t - δ ≤ max w (t - δ) := le_max_right _ _
        have ht'4 : max w (t - δ) ≤ t := max_le ht1 (by linarith)
        rw [← ih _ ht'1 ht'2]
        by_contra hne
        have ht : 0 < t := by linarith
        have ht' : 0 < max w (t - δ) := by linarith
        have hdiff : (t - max w (t - δ)) ^ 2 ≤ δ ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        have hsum : 2 * w ≤ t + max w (t - δ) := by linarith
        have hcw := mul_pos hdp hw
        rcases hval t ht with h | h <;> rcases hval _ ht' with h' | h'
        · exact hne (by rw [h, h'])
        · have := hsep _ t ht' ht h' h
          nlinarith [mul_le_mul_of_nonneg_left hsum hdp.le]
        · have := hsep t _ ht ht' h h'
          nlinarith [mul_le_mul_of_nonneg_left hsum hdp.le]
        · exact hne (by rw [h, h'])
    intro t ht
    obtain ⟨k, hk⟩ := exists_nat_gt ((t - w) / δ)
    rw [div_lt_iff₀ hδ] at hk
    exact claim k t ht (by linarith)
  intro x hx
  rcases hval x hx with h | h
  · exfalso
    have e1 := hmarch x hx (max x p) (le_max_left _ _)
    have e2 := hmarch p hp (max x p) (le_max_right _ _)
    linarith
  · linarith

/-- IMO 2026 Problem 5: the solutions are exactly the shifts `x ↦ x + c`, `c ≥ 0`. -/
theorem imo2026_p5 (f : ℝ → ℝ) :
    Good f ↔ ∃ c, 0 ≤ c ∧ ∀ x, 0 < x → f x = x + c :=
  ⟨shift_of_good f, fun ⟨c, hc, hf⟩ => good_of_shift c hc f hf⟩

end Ascent.IMO2026P5

#print axioms Ascent.IMO2026P5.imo2026_p5
