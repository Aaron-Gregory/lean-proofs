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

end Ascent.IMO2026P6

#print axioms Ascent.IMO2026P6.mem_range_iff
