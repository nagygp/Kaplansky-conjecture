import Mathlib

/-!
# Weighted shift matrices over `ZMod n`

This file develops the matrix algebra needed for the determinant computation of the
semifield family constructed in the paper (Theorem `thm:division`).

A *weighted shift* matrix `shiftM a t` has `(i, i + a)` entry `t i` and all other entries
zero.  These matrices are closed under multiplication, and the determinant of
`z • 1 + shiftM a t` is `z ^ n + ∏ i, t i` whenever `n` is odd and `a ≠ 0` is a unit of
`ZMod n`.  This is the "weighted cycle" computation `eq:weighted-cycle` of the paper.
-/

namespace Semifields

open scoped BigOperators
open Matrix

variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- The weighted shift matrix: its `(i, i + a)` entry is `t i`, all other entries are `0`. -/
def shiftM (a : ZMod n) (t : ZMod n → R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.of fun i j => if j = i + a then t i else 0

omit [NeZero n] in
@[simp] lemma shiftM_apply (a : ZMod n) (t : ZMod n → R) (i j : ZMod n) :
    shiftM a t i j = if j = i + a then t i else 0 := rfl

omit [NeZero n] in
lemma shiftM_congr_fun (a : ZMod n) {t u : ZMod n → R} (h : ∀ i, t i = u i) :
    shiftM a t = shiftM a u := by
  rw [funext h]

omit [NeZero n] in
@[simp] lemma shiftM_zero_fun (a : ZMod n) : shiftM a (fun _ => (0 : R)) = 0 := by
  ext i j
  by_cases h : j = i + a <;> simp [shiftM, h]

omit [NeZero n] in
lemma shiftM_add (a : ZMod n) (t u : ZMod n → R) :
    shiftM a t + shiftM a u = shiftM a (fun i => t i + u i) := by
  ext i j
  by_cases h : j = i + a <;> simp [shiftM, h]

omit [NeZero n] in
lemma shiftM_smul (c : R) (a : ZMod n) (t : ZMod n → R) :
    c • shiftM a t = shiftM a (fun i => c * t i) := by
  ext i j
  by_cases h : j = i + a <;> simp [shiftM, h]

omit [NeZero n] in
lemma shiftM_neg (a : ZMod n) (t : ZMod n → R) :
    -shiftM a t = shiftM a (fun i => -t i) := by
  ext i j
  by_cases h : j = i + a <;> simp [shiftM, h]

omit [NeZero n] in
lemma shiftM_zero_eq_diagonal (t : ZMod n → R) :
    shiftM (0 : ZMod n) t = Matrix.diagonal t := by
  ext i j
  by_cases h : j = i <;> simp [shiftM, Matrix.diagonal, h, eq_comm]

omit [NeZero n] in
lemma smul_one_eq_shiftM (z : R) :
    z • (1 : Matrix (ZMod n) (ZMod n) R) = shiftM (0 : ZMod n) (fun _ => z) := by
  rw [shiftM_zero_eq_diagonal]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.diagonal]

omit [NeZero n] in
lemma one_eq_shiftM : (1 : Matrix (ZMod n) (ZMod n) R) = shiftM (0 : ZMod n) (fun _ => 1) := by
  simpa using smul_one_eq_shiftM (n := n) (1 : R)

/-- Weighted shift matrices multiply as expected. -/
lemma shiftM_mul (a b : ZMod n) (t u : ZMod n → R) :
    shiftM a t * shiftM b u = shiftM (a + b) (fun i => t i * u (i + a)) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : j = i + (a + b)
  · rw [Finset.sum_eq_single (i + a)]
    · simp [h, add_assoc]
    · intro k _ hk
      simp [hk]
    · intro hk; exact absurd (Finset.mem_univ _) hk
  · rw [shiftM_apply, if_neg h]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hk : k = i + a
    · subst hk
      have hj : ¬ (j = i + a + b) := by rw [add_assoc]; exact h
      simp [hj]
    · simp [hk]

@[simp] lemma det_shiftM_zero (t : ZMod n → R) :
    (shiftM (0 : ZMod n) t).det = ∏ i, t i := by
  rw [shiftM_zero_eq_diagonal, Matrix.det_diagonal]

/-- The additive shift permutation `x ↦ x + a` of `ZMod n`. -/
def shiftPerm (a : ZMod n) : Equiv.Perm (ZMod n) := Equiv.addRight a

omit [NeZero n] in
@[simp] lemma shiftPerm_apply (a : ZMod n) (i : ZMod n) : shiftPerm a i = i + a := rfl

omit [NeZero n] in
lemma shiftPerm_pow (a : ZMod n) (k : ℕ) : ∀ i : ZMod n,
    ((shiftPerm a) ^ k) i = i + k • a := by
  induction k with
  | zero => simp
  | succ m ih =>
      intro i
      rw [pow_succ]
      simp only [Equiv.Perm.mul_apply, shiftPerm, Equiv.coe_addRight] at *
      rw [ih (i + a), succ_nsmul]
      ring

omit [NeZero n] in
lemma shiftPerm_pow_card (a : ZMod n) : (shiftPerm a) ^ n = 1 := by
  ext i
  rw [shiftPerm_pow]
  simp [nsmul_eq_mul]

/-- A shift permutation of `ZMod n` with `n` odd is an even permutation. -/
lemma sign_shiftPerm (a : ZMod n) (hodd : Odd n) : Equiv.Perm.sign (shiftPerm a) = 1 := by
  have h : (Equiv.Perm.sign (shiftPerm (n := n) a)) ^ n = 1 := by
    rw [← map_pow, shiftPerm_pow_card, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (shiftPerm (n := n) a)) with h1 | h1
  · exact h1
  · rw [h1, hodd.neg_one_pow] at h
    exact absurd h (by decide)

/-- If a permutation of `ZMod n` moves every point either not at all or by the unit `a`,
then it is the identity or the shift by `a`. -/
lemma eq_one_or_shiftPerm {σ : Equiv.Perm (ZMod n)} {a : ZMod n} (ha : IsUnit a)
    (h : ∀ i, σ i = i ∨ σ i = i + a) : σ = 1 ∨ σ = shiftPerm a := by
  classical
  set S := Finset.univ.filter (fun i : ZMod n => σ i ≠ i) with hS
  have hsum : ∑ i : ZMod n, (σ i - i) = 0 := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i : ZMod n, σ i = ∑ i : ZMod n, i := Equiv.sum_comp σ (fun i => i)
    rw [this, sub_self]
  have hsum2 : ∑ i : ZMod n, (σ i - i) = S.card • a := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ZMod n => σ i ≠ i)]
    have h1 : ∑ i ∈ S, (σ i - i) = S.card • a := by
      rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const]
      have hthis := h i
      simp only [hS, Finset.mem_filter] at hi
      rcases hthis with h' | h'
      · exact absurd h' hi.2
      · rw [h']; ring
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : ZMod n => ¬ (σ i ≠ i)), (σ i - i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp only [Finset.mem_filter, not_not] at hi
      rw [hi.2, sub_self]
    rw [h1, h2, add_zero]
  rw [hsum2, nsmul_eq_mul] at hsum
  have hcard : ((S.card : ZMod n)) = 0 := by
    rcases ha with ⟨u, hu⟩
    have hmul := congrArg (· * (↑u⁻¹ : ZMod n)) hsum
    simp only [zero_mul] at hmul
    rw [mul_assoc, ← hu] at hmul
    simpa using hmul
  have hdvd : n ∣ S.card := (ZMod.natCast_eq_zero_iff _ _).mp hcard
  have hle : S.card ≤ n := by
    simpa [ZMod.card] using Finset.card_le_univ S
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · left
    ext i
    have hi : i ∉ S := by simp [Finset.card_eq_zero.mp h0]
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simpa using hi
  · right
    have hcardn : S.card = n := Nat.le_antisymm hle (Nat.le_of_dvd hpos hdvd)
    have huniv : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hcardn, ZMod.card])
    ext i
    have hi : i ∈ S := huniv ▸ Finset.mem_univ i
    rw [hS] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases h i with h' | h'
    · exact absurd h' hi
    · simpa [shiftPerm] using h'

/-- **Weighted cycle determinant.**  For `n` odd and `a` a nonzero unit of `ZMod n`,
`det (z • 1 + shiftM a t) = z ^ n + ∏ i, t i`. -/
theorem det_smul_one_add_shiftM (z : R) {a : ZMod n} (ha : IsUnit a) (ha0 : a ≠ 0)
    (hodd : Odd n) (t : ZMod n → R) :
    (z • (1 : Matrix (ZMod n) (ZMod n) R) + shiftM a t).det = z ^ n + ∏ i, t i := by
  classical
  set M := z • (1 : Matrix (ZMod n) (ZMod n) R) + shiftM a t with hM
  have hMapply : ∀ i j, M i j = (if i = j then z else 0) + (if j = i + a then t i else 0) := by
    intro i j; simp [hM, shiftM, Matrix.one_apply, Matrix.smul_apply]
  have hia : ∀ i : ZMod n, ¬ (i = i + a) := fun i h => ha0 (by simpa using h.symm)
  have hne : (1 : Equiv.Perm (ZMod n)) ≠ shiftPerm a := by
    intro hcon
    have hc := congrArg (fun f => f 0) hcon
    simp [shiftPerm] at hc
    exact ha0 hc.symm
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have hvanish : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (ZMod n))),
      σ ∉ ({1, shiftPerm a} : Finset (Equiv.Perm (ZMod n))) →
      Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i = 0 := by
    intro σ _ hσ
    have hex : ∃ i, ¬ (σ i = i ∨ σ i = i + a) := by
      by_contra hc
      push_neg at hc
      rcases eq_one_or_shiftPerm ha (fun i => hc i) with h1 | h1 <;> simp [h1] at hσ
    obtain ⟨i, hi⟩ := hex
    push_neg at hi
    have hzero : ∏ i, Mᵀ (σ i) i = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      show M i (σ i) = 0
      rw [hMapply, if_neg (fun h => hi.1 h.symm), if_neg hi.2]
      ring
    rw [hzero, smul_zero]
  rw [← Finset.sum_subset
    (Finset.subset_univ ({1, shiftPerm a} : Finset (Equiv.Perm (ZMod n)))) hvanish]
  rw [Finset.sum_pair hne, sign_shiftPerm a hodd]
  simp only [map_one, one_smul]
  congr 1
  · have hprod : ∀ i : ZMod n, Mᵀ ((1 : Equiv.Perm (ZMod n)) i) i = z := by
      intro i; show M i i = z
      rw [hMapply, if_pos rfl, if_neg (hia i), add_zero]
    rw [Finset.prod_congr rfl (fun i _ => hprod i)]
    simp [ZMod.card]
  · have hprod : ∀ i : ZMod n, Mᵀ ((shiftPerm a) i) i = t i := by
      intro i; show M i (i + a) = t i
      rw [hMapply, if_neg (hia i), if_pos rfl, zero_add]
    rw [Finset.prod_congr rfl (fun i _ => hprod i)]

end Semifields
