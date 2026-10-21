import Mathlib

/-!
# Erdős #473 (JSP-000385), combinatorial half

Erdős #473 asks for a permutation `a₁, a₂, …` of the positive integers with every
`aₖ + aₖ₊₁` prime. We do NOT prove the number theory. We prove:

1. `hamiltonian_ray`: if a relation `Adj` on `ℕ` is *connected around finite sets*
   (any `x` reaches any `m ∉ F` through fresh vertices outside the finite set `F`),
   then there is a bijection `a : ℕ → ℕ` with `Adj (a n) (a (n+1))` for all `n`.
2. `erdos473_of_connected`: hence #473 follows from that connectivity hypothesis
   for the prime-sum graph. The hypothesis is left explicit and unproved.
-/

namespace Ascent

open List

/-- Any `x` can reach any `m ∉ F` (with `x ≠ m`) by a path whose interior vertices are
distinct, avoid `F`, and avoid `m`. -/
def ConnectedAroundFinite (Adj : ℕ → ℕ → Prop) : Prop :=
  ∀ (F : Finset ℕ) (x m : ℕ), m ∉ F → x ≠ m →
    ∃ l : List ℕ, IsChain Adj (x :: (l ++ [m])) ∧ l.Nodup ∧ ∀ v ∈ l, v ∉ F ∧ v ≠ m

section Ray

variable {Adj : ℕ → ℕ → Prop} (H : ConnectedAroundFinite Adj)

/-- One step of the construction: if `k` is missing, walk from the end of `P` to `k`. -/
noncomputable def step (k : ℕ) (P : List ℕ) : List ℕ :=
  if h : k ∉ P ∧ P.getLast?.getD 0 ≠ k then
    P ++ (Classical.choose (H P.toFinset (P.getLast?.getD 0) k (by simpa using h.1) h.2)) ++ [k]
  else P

/-- The growing path after handling `0, …, k-1`. -/
noncomputable def path : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => step H k (path k)

lemma getLast?_eq_some_getD {P : List ℕ} (hP : P ≠ []) :
    P.getLast? = some (P.getLast?.getD 0) := by
  cases h : P.getLast? with
  | none => simp_all
  | some y => rfl

lemma step_spec (k : ℕ) {P : List ℕ} (hP : P ≠ []) (hc : IsChain Adj P) (hn : P.Nodup) :
    step H k P ≠ [] ∧ IsChain Adj (step H k P) ∧ (step H k P).Nodup ∧ k ∈ step H k P ∧
      P <+: step H k P := by
  unfold step
  split_ifs with h
  · set x := P.getLast?.getD 0 with hx
    obtain ⟨hch, hnd, hav⟩ :=
      Classical.choose_spec (H P.toFinset x k (by simpa using h.1) h.2)
    set l := Classical.choose (H P.toFinset x k (by simpa using h.1) h.2)
    have hlast : P.getLast? = some x := getLast?_eq_some_getD hP
    refine ⟨by simp, ?_, ?_, by simp, ?_⟩
    · rw [List.append_assoc]
      rw [isChain_cons] at hch
      refine hc.append hch.2 ?_
      intro a ha b hb
      rw [hlast] at ha
      cases ha
      exact hch.1 b hb
    · rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨hn, hnd, ?_⟩, by simp, ?_⟩
      · intro a ha b hb hab
        subst hab
        exact (hav a hb).1 (by simpa using ha)
      · intro a ha b hb hab
        simp at hb
        subst hb
        subst hab
        rcases List.mem_append.1 ha with ha | ha
        · exact h.1 ha
        · exact (hav a ha).2 rfl
    · rw [List.append_assoc]
      exact List.prefix_append _ _
  · refine ⟨hP, hc, hn, ?_, List.prefix_refl _⟩
    by_contra hk
    apply h
    refine ⟨hk, ?_⟩
    intro hxk
    apply hk
    rw [← hxk]
    exact List.mem_of_getLast? (getLast?_eq_some_getD hP)

lemma path_spec (k : ℕ) :
    path H k ≠ [] ∧ IsChain Adj (path H k) ∧ (path H k).Nodup ∧ ∀ i < k, i ∈ path H k := by
  induction k with
  | zero => simp [path]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨s1, s2, s3, s4, s5⟩ := step_spec H k h1 h2 h3
    refine ⟨s1, s2, s3, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact s5.subset (h4 i hi)
    · subst hi; exact s4

lemma path_prefix {j k : ℕ} (hjk : j ≤ k) : path H j <+: path H k := by
  induction k, hjk using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih =>
    obtain ⟨h1, h2, h3, _⟩ := path_spec H k
    exact ih.trans (step_spec H k h1 h2 h3).2.2.2.2

lemma le_length_path (k : ℕ) : k ≤ (path H k).length := by
  obtain ⟨_, _, _, h4⟩ := path_spec H k
  have := (List.nodup_range (n := k)).subperm (fun i hi => h4 i (List.mem_range.1 hi))
  simpa using this.length_le

/-- The ray: `a n` is the `n`-th vertex of the path. -/
noncomputable def ray (n : ℕ) : ℕ :=
  (path H (n + 1))[n]'(by have := le_length_path H (n + 1); omega)

lemma ray_eq (n K : ℕ) (hn : n < (path H K).length) : ray H n = (path H K)[n] := by
  unfold ray
  rcases le_total (n + 1) K with h | h
  · exact (path_prefix H h).getElem _
  · exact ((path_prefix H h).getElem hn).symm

theorem hamiltonian_ray (H : ConnectedAroundFinite Adj) :
    ∃ a : ℕ → ℕ, Function.Bijective a ∧ ∀ n, Adj (a n) (a (n + 1)) := by
  refine ⟨ray H, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have hK := le_length_path H (max i j + 1)
    have hi : i < (path H (max i j + 1)).length := by omega
    have hj : j < (path H (max i j + 1)).length := by omega
    rw [ray_eq H i _ hi, ray_eq H j _ hj] at hij
    exact ((path_spec H _).2.2.1.getElem_inj_iff).1 hij
  · intro m
    have hm : m ∈ path H (m + 1) := (path_spec H (m + 1)).2.2.2 m (Nat.lt_succ_self m)
    obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hm
    exact ⟨i, by rw [ray_eq H i _ hi, hmi]⟩
  · intro n
    have hK := le_length_path H (n + 2)
    have h1 : n < (path H (n + 2)).length := by omega
    have h2 : n + 1 < (path H (n + 2)).length := by omega
    rw [ray_eq H n _ h1, ray_eq H (n + 1) _ h2]
    exact (List.isChain_iff_getElem.1 (path_spec H (n + 2)).2.1) n h2

end Ray

/-- The prime-sum graph on positive integers, shifted to `ℕ` (vertex `v` means `v + 1`). -/
def PrimeSumAdj (a b : ℕ) : Prop := (a + 1 + (b + 1)).Prime

/-- Erdős #473, conditional on connectivity of the prime-sum graph around finite sets. -/
theorem erdos473_of_connected (H : ConnectedAroundFinite PrimeSumAdj) :
    ∃ a : ℕ → ℕ, Function.Injective a ∧ Set.range a = {n | 0 < n} ∧
      ∀ k, (a k + a (k + 1)).Prime := by
  obtain ⟨σ, ⟨hinj, hsurj⟩, hadj⟩ := hamiltonian_ray H
  refine ⟨fun n => σ n + 1, ?_, ?_, fun k => hadj k⟩
  · intro i j hij
    exact hinj (by simpa using hij)
  · ext n
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, rfl⟩; omega
    · intro hn
      obtain ⟨k, hk⟩ := hsurj (n - 1)
      exact ⟨k, by omega⟩

/-! ## From a Goldbach-type hypothesis to connectivity -/

/-- Goldbach-type hypothesis: every odd `N` is `p + r - q` with primes `p, q, r` all above any
bound. (A 3-edge path `x → y → z → m` in the prime-sum graph needs exactly this with
`N = x + m`.) Left unproved. -/
def LargePrimesHypothesis : Prop :=
  ∀ N B : ℕ, Odd N → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ B < p ∧ B < q ∧ B < r ∧
    p + r = q + N

lemma odd_of_prime_gt {p : ℕ} (hp : p.Prime) (h : 2 < p) : ∃ a, p = 2 * a + 1 := by
  obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
  exact ⟨a, ha⟩

lemma lt_of_gt_sup {F : Finset ℕ} {v : ℕ} (h : F.sup id < v) : v ∉ F := by
  intro hv
  have := Finset.le_sup (f := id) hv
  simp at this
  omega

/-- Three edges `x → y → z → m` through fresh vertices, when `x + m` is odd (shifted). -/
lemma three_step (G : LargePrimesHypothesis) (F : Finset ℕ) (x m : ℕ)
    (hpar : Odd (x + 1 + (m + 1))) :
    ∃ y z, PrimeSumAdj x y ∧ PrimeSumAdj y z ∧ PrimeSumAdj z m ∧ y ∉ F ∧ z ∉ F ∧
      y ≠ m ∧ z ≠ m ∧ y ≠ z := by
  set B := F.sup id + 2 * x + 2 * m + 10 with hB
  obtain ⟨p, q, r, hp, hq, hr, hpB, hqB, hrB, hsum⟩ := G _ B hpar
  obtain ⟨a, ha⟩ := odd_of_prime_gt hp (by omega)
  obtain ⟨b, hb⟩ := odd_of_prime_gt hr (by omega)
  obtain ⟨c, hc⟩ := hpar
  refine ⟨p - x - 2, r - m - 2, ?_, ?_, ?_, lt_of_gt_sup (by omega), lt_of_gt_sup (by omega),
    by omega, by omega, by omega⟩
  · unfold PrimeSumAdj
    have : x + 1 + (p - x - 2 + 1) = p := by omega
    rw [this]; exact hp
  · unfold PrimeSumAdj
    have : p - x - 2 + 1 + (r - m - 2 + 1) = q := by omega
    rw [this]; exact hq
  · unfold PrimeSumAdj
    have : r - m - 2 + 1 + (m + 1) = r := by omega
    rw [this]; exact hr

theorem connected_of_largePrimes (G : LargePrimesHypothesis) :
    ConnectedAroundFinite PrimeSumAdj := by
  intro F x m hmF hxm
  rcases Nat.even_or_odd (x + 1 + (m + 1)) with hev | hodd
  · -- one edge to a fresh `w`, then three edges from `w` to `m`
    obtain ⟨p0, hp0B, hp0⟩ := Nat.exists_infinite_primes (F.sup id + 2 * x + 2 * m + 10)
    obtain ⟨a, ha⟩ := odd_of_prime_gt hp0 (by omega)
    obtain ⟨e, he⟩ := hev
    set w := p0 - x - 2 with hw
    have hwpar : Odd (w + 1 + (m + 1)) := ⟨a + m + 1 - e, by omega⟩
    obtain ⟨y, z, hwy, hyz, hzm, hyF, hzF, hym, hzm', hyz'⟩ :=
      three_step G (insert w F) w m hwpar
    simp only [Finset.mem_insert, not_or] at hyF hzF
    refine ⟨[w, y, z], ?_, ?_, ?_⟩
    · have hxw : PrimeSumAdj x w := by
        unfold PrimeSumAdj
        have : x + 1 + (w + 1) = p0 := by omega
        rw [this]; exact hp0
      simp [isChain_cons_cons, hxw, hwy, hyz, hzm]
    · have h1 : w ≠ y := fun h => hyF.1 h.symm
      have h2 : w ≠ z := fun h => hzF.1 h.symm
      simp [h1, h2, hyz']
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨lt_of_gt_sup (by omega), by omega⟩
      · exact ⟨hyF.2, hym⟩
      · exact ⟨hzF.2, hzm'⟩
  · obtain ⟨y, z, hxy, hyz, hzm, hyF, hzF, hym, hzm', hyz'⟩ := three_step G F x m hodd
    refine ⟨[y, z], ?_, ?_, ?_⟩
    · simp [isChain_cons_cons, hxy, hyz, hzm]
    · simp [hyz']
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hyF, hym⟩
      · exact ⟨hzF, hzm'⟩

/-- Erdős #473 from the Goldbach-type hypothesis alone. -/
theorem erdos473_of_largePrimes (G : LargePrimesHypothesis) :
    ∃ a : ℕ → ℕ, Function.Injective a ∧ Set.range a = {n | 0 < n} ∧
      ∀ k, (a k + a (k + 1)).Prime :=
  erdos473_of_connected (connected_of_largePrimes G)

end Ascent

#print axioms Ascent.hamiltonian_ray
#print axioms Ascent.erdos473_of_connected
#print axioms Ascent.erdos473_of_largePrimes
