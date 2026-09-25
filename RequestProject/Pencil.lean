import Mathlib

/-!
# Linear matrix pencils, pencil isotopy and the monomial lemma

A *linear pencil* is a matrix whose entries are linear forms in variables `X k`; we record it
by its coefficient matrices `p k`, so that its value at `X` is `∑ k, X k • p k`.  The value can
be taken over any commutative `F`-algebra, in particular over the polynomial ring.

This file proves the abstract matrix facts behind Lemma `lem:monomial` of the paper:

* `PencilIso pQ pP M₁ M₂ M₃` is the matrix form `L_Q(M₁ X) M₂ = M₃ L_P(X)` of an isotopism
  (`eq:pencilisotopy`); it extends from `F` to every `F`-algebra (`pencilIso_lift`).
* `row_monomial_of_pencilIso` : if both determinants are nonzero multiples of the coordinate
  product, the matrix `M₁` is monomial (unique factorisation, via primality of the variables).
* `pencilIso_rotate` : for a pencil whose trilinear form is cyclically symmetric, an isotopism
  `(M₁, M₂, M₃)` gives an isotopism `(M₂, M₃⁻ᵀ, M₁⁻ᵀ)`; this is how the paper uses the trace
  determinant to control the third component.
* `inv_transpose_row_monomial` : the inverse transpose of an invertible monomial matrix is
  monomial.
-/

namespace Semifields

open scoped BigOperators
open Matrix

section Pencil

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

/-- The value `∑ k, X k • p k` of the linear pencil with coefficient matrices `p k`, over an
`F`-algebra `R`. -/
noncomputable def pen {R : Type*} [CommRing R] [Algebra F R] (p : ι → Matrix ι ι F)
    (X : ι → R) : Matrix ι ι R :=
  ∑ k, X k • (p k).map (algebraMap F R)

omit [DecidableEq ι] in
lemma pen_apply {R : Type*} [CommRing R] [Algebra F R] (p : ι → Matrix ι ι F) (X : ι → R)
    (i j : ι) : pen p X i j = ∑ k, X k * algebraMap F R (p k i j) := by
  simp [pen, Matrix.sum_apply]

omit [DecidableEq ι] in
lemma pen_self_apply (p : ι → Matrix ι ι F) (X : ι → F) (i j : ι) :
    pen p X i j = ∑ k, X k * p k i j := by
  simp [pen_apply]

lemma pen_single (p : ι → Matrix ι ι F) (k : ι) : pen p (Pi.single k (1 : F)) = p k := by
  ext i j
  rw [pen_self_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The matrix form `L_Q(M₁ X) M₂ = M₃ L_P(X)` of an isotopism between two pencils. -/
def PencilIso (pQ pP : ι → Matrix ι ι F) (M₁ M₂ M₃ : Matrix ι ι F) : Prop :=
  ∀ X : ι → F, pen pQ (M₁ *ᵥ X) * M₂ = M₃ * pen pP X

/-- The defect of a pencil isotopy is itself a linear pencil. -/
lemma pencil_defect {R : Type*} [CommRing R] [Algebra F R] (pQ pP : ι → Matrix ι ι F)
    (M₁ M₂ M₃ : Matrix ι ι F) (Y : ι → R) :
    pen pQ ((M₁.map (algebraMap F R)) *ᵥ Y) * M₂.map (algebraMap F R)
        - M₃.map (algebraMap F R) * pen pP Y
      = pen (fun k => pen pQ (M₁ *ᵥ Pi.single k 1) * M₂ - M₃ * pP k) Y := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, pen_apply, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sub, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_sub_distrib, mul_sub]
  congr 1
  · simp only [Pi.single_apply, Algebra.algebraMap_self, RingHom.id_apply,
      apply_ite (algebraMap F R), map_one, map_zero, mul_ite, mul_one, mul_zero]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
    simp only [if_true]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

lemma pencilIso_iff (pQ pP : ι → Matrix ι ι F) (M₁ M₂ M₃ : Matrix ι ι F) :
    PencilIso pQ pP M₁ M₂ M₃ ↔ ∀ k, pen pQ (M₁ *ᵥ Pi.single k 1) * M₂ = M₃ * pP k := by
  constructor
  · intro h k
    have := h (Pi.single k 1)
    rwa [pen_single] at this
  · intro h X
    have hd := pencil_defect (R := F) pQ pP M₁ M₂ M₃ X
    have hz : (fun k => pen pQ (M₁ *ᵥ Pi.single k 1) * M₂ - M₃ * pP k) = fun _ => 0 := by
      funext k; rw [h k, sub_self]
    rw [hz] at hd
    have h0 : pen (fun _ => (0 : Matrix ι ι F)) X = 0 := by simp [pen]
    rw [h0] at hd
    simpa [Matrix.map_id', sub_eq_zero] using hd

/-- A pencil isotopy over `F` holds over every commutative `F`-algebra. -/
theorem pencilIso_lift {pQ pP : ι → Matrix ι ι F} {M₁ M₂ M₃ : Matrix ι ι F}
    (h : PencilIso pQ pP M₁ M₂ M₃) {R : Type*} [CommRing R] [Algebra F R] (Y : ι → R) :
    pen pQ ((M₁.map (algebraMap F R)) *ᵥ Y) * M₂.map (algebraMap F R)
      = M₃.map (algebraMap F R) * pen pP Y := by
  have hd := pencil_defect pQ pP M₁ M₂ M₃ Y
  have hz : (fun k => pen pQ (M₁ *ᵥ Pi.single k 1) * M₂ - M₃ * pP k) = fun _ => 0 := by
    funext k; rw [(pencilIso_iff pQ pP M₁ M₂ M₃).mp h k, sub_self]
  rw [hz] at hd
  have h0 : pen (fun _ => (0 : Matrix ι ι F)) Y = 0 := by simp [pen]
  rw [h0, sub_eq_zero] at hd
  exact hd

end Pencil

section Monomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

open MvPolynomial

/-- Every row of `M` has exactly one nonzero entry. -/
def RowMonomial (M : Matrix ι ι F) : Prop :=
  ∀ i, ∃ j, M i j ≠ 0 ∧ ∀ k, k ≠ j → M i k = 0

omit [DecidableEq ι] in
lemma mulVec_X_eq (M : Matrix ι ι F) (i : ι) :
    ((M.map (algebraMap F (MvPolynomial ι F))) *ᵥ (fun k => X k)) i = ∑ k, C (M i k) * X k := by
  simp [mulVec, dotProduct, MvPolynomial.algebraMap_eq]

omit [DecidableEq ι] in
lemma coeff_linear (a : ι → F) (k : ι) :
    coeff (Finsupp.single k 1) (∑ l, C (a l) * (X l : MvPolynomial ι F)) = a k := by
  classical
  simp only [coeff_sum, coeff_C_mul, coeff_X']
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro h
      exact hb ((Finsupp.single_left_inj one_ne_zero).mp h)
  · intro h; exact absurd (Finset.mem_univ k) h

omit [DecidableEq ι] in
lemma coeff_eq_zero_of_X_dvd {j : ι} {a : ι → F}
    (h : (X j : MvPolynomial ι F) ∣ ∑ l, C (a l) * X l) : ∀ k, k ≠ j → a k = 0 := by
  classical
  intro k hk
  obtain ⟨g, hg⟩ := h
  have := congrArg (coeff (Finsupp.single k 1)) hg
  rw [coeff_linear, coeff_X_mul'] at this
  rw [this, if_neg]
  simp [Finsupp.support_single_ne_zero, Ne.symm hk]

/-- **Lemma `lem:monomial`, matrix form.**  If the determinants of the two pencils are nonzero
multiples of the coordinate product, then the first matrix of a pencil isotopy is monomial. -/
theorem rowMonomial_of_pencilIso {pQ pP : ι → Matrix ι ι F} {M₁ M₂ M₃ : Matrix ι ι F}
    (h : PencilIso pQ pP M₁ M₂ M₃) (κQ κP : F)
    (hQ : ∀ Y : ι → MvPolynomial ι F, (pen pQ Y).det = C κQ * ∏ i, Y i)
    (hP : (pen pP (fun i => (X i : MvPolynomial ι F))).det = C κP * ∏ i, X i)
    (hκP : κP ≠ 0) (hM₃ : M₃.det ≠ 0) : RowMonomial M₁ := by
  classical
  have hl := pencilIso_lift h (R := MvPolynomial ι F) (fun i => X i)
  have hdet := congrArg Matrix.det hl
  rw [det_mul, det_mul, hQ, hP] at hdet
  have hmapdet : ∀ M : Matrix ι ι F, (M.map (algebraMap F (MvPolynomial ι F))).det = C M.det := by
    intro M
    rw [← MvPolynomial.algebraMap_eq]
    exact ((algebraMap F (MvPolynomial ι F)).map_det M).symm
  rw [hmapdet, hmapdet] at hdet
  set ℓ : ι → MvPolynomial ι F := (M₁.map (algebraMap F (MvPolynomial ι F))) *ᵥ (fun i => X i)
    with hℓdef
  have hℓi : ∀ i, ℓ i = ∑ k, C (M₁ i k) * X k := fun i => mulVec_X_eq M₁ i
  have hprodX : (∏ i, (X i : MvPolynomial ι F)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero i)
  have hRHS : C M₃.det * (C κP * ∏ i, (X i : MvPolynomial ι F)) ≠ 0 := by
    refine mul_ne_zero ?_ (mul_ne_zero ?_ hprodX)
    · simpa using hM₃
    · simpa using hκP
  rw [← hdet] at hRHS
  have hprodℓ : (∏ i, ℓ i) ≠ 0 := fun h0 => hRHS (by rw [h0]; ring)
  have hℓ : ∀ i, ℓ i ≠ 0 := fun i => (Finset.prod_ne_zero_iff.mp hprodℓ) i (Finset.mem_univ i)
  have hconst : C κQ * C M₂.det ≠ (0 : MvPolynomial ι F) := fun h0 => hRHS (by
    rw [show (C κQ * ∏ i, ℓ i) * C M₂.det = (C κQ * C M₂.det) * ∏ i, ℓ i by ring, h0, zero_mul])
  have hunit : IsUnit (C κQ * C M₂.det : MvPolynomial ι F) := by
    rw [← map_mul] at hconst ⊢
    have : κQ * M₂.det ≠ 0 := fun h0 => hconst (by rw [h0, map_zero])
    exact (isUnit_iff_ne_zero.mpr this).map C
  have hdvd : ∀ j, ∃ i, (X j : MvPolynomial ι F) ∣ ℓ i := by
    intro j
    have h1 : (X j : MvPolynomial ι F) ∣ (C κQ * C M₂.det) * ∏ i, ℓ i := by
      rw [show (C κQ * C M₂.det) * ∏ i, ℓ i = (C κQ * ∏ i, ℓ i) * C M₂.det by ring, hdet]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun i => (X i : MvPolynomial ι F)) (Finset.mem_univ j)) _) _
    rcases (X_prime (R := F) (i := j)).dvd_or_dvd h1 with h2 | h2
    · exact absurd (isUnit_of_dvd_unit h2 hunit) (X_prime (R := F) (i := j)).not_unit
    · obtain ⟨i, -, hi⟩ := ((X_prime (R := F) (i := j)).dvd_finset_prod_iff _).mp h2
      exact ⟨i, hi⟩
  choose π hπ using hdvd
  have hzero : ∀ j k, k ≠ j → M₁ (π j) k = 0 := fun j =>
    coeff_eq_zero_of_X_dvd (by rw [← hℓi]; exact hπ j)
  have hℓzero : ∀ i, (∀ k, M₁ i k = 0) → ℓ i = 0 := by
    intro i hi
    rw [hℓi]
    exact Finset.sum_eq_zero (fun k _ => by rw [hi k, map_zero, zero_mul])
  have hinj : Function.Injective π := by
    intro j j' hjj'
    by_contra hne
    apply hℓ (π j)
    refine hℓzero _ (fun k => ?_)
    by_cases hk : k = j
    · subst hk
      rw [hjj']
      exact hzero j' k hne
    · exact hzero j k hk
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  refine ⟨j, fun hj0 => hℓ (π j) (hℓzero _ (fun k => ?_)), hzero j⟩
  by_cases hk : k = j
  · subst hk; exact hj0
  · exact hzero j k hk

/-- The inverse transpose of an invertible monomial matrix is monomial. -/
theorem rowMonomial_inv_transpose {N : Matrix ι ι F} (hN : RowMonomial N) (hdet : N.det ≠ 0) :
    RowMonomial (Nᵀ)⁻¹ := by
  choose π hπ0 hπ using hN
  have hinj : Function.Injective π := by
    by_contra hni
    have hns : ¬ Function.Surjective π := fun hs =>
      hni (Finite.injective_iff_surjective.mpr hs)
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨j, hj⟩ := hns
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero j (fun i => hπ i j (fun h => hj i h.symm)))
  have hbij : Function.Bijective π := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  let M : Matrix ι ι F := Matrix.of fun i j => if j = π i then (N i (π i))⁻¹ else 0
  have hM : Nᵀ * M = 1 := by
    ext a b
    obtain ⟨i0, rfl⟩ := hbij.2 b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single i0]
    · rw [if_pos rfl]
      by_cases hab : a = π i0
      · subst hab
        rw [if_pos rfl]
        exact mul_inv_cancel₀ (hπ0 i0)
      · rw [if_neg hab, hπ i0 a hab, zero_mul]
    · intro i _ hi
      rw [if_neg, mul_zero]
      intro hb
      exact hi (hinj hb.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.inv_eq_right_inv hM]
  intro i
  refine ⟨π i, ?_, fun k hk => ?_⟩
  · simp only [M, Matrix.of_apply, if_true]
    exact inv_ne_zero (hπ0 i)
  · simp only [M, Matrix.of_apply, if_neg hk]

/-- The trilinear form `Z ⬝ (L(X) Y)` of a pencil is invariant under cyclic permutations. -/
def PencilCyclic (p : ι → Matrix ι ι F) : Prop :=
  ∀ X Y Z : ι → F, Z ⬝ᵥ (pen p X *ᵥ Y) = X ⬝ᵥ (pen p Y *ᵥ Z)

omit [DecidableEq ι] in
lemma matrix_ext_dot {A B : Matrix ι ι F}
    (h : ∀ X Z : ι → F, X ⬝ᵥ (A *ᵥ Z) = X ⬝ᵥ (B *ᵥ Z)) : A = B := by
  classical
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using this

/-- **Cyclic rotation of a pencil isotopy.**  For a pencil with cyclically symmetric
trilinear form, an isotopy `(M₁, M₂, M₃)` gives the isotopy `(M₂, M₃⁻ᵀ, M₁⁻ᵀ)`. -/
theorem pencilIso_rotate {p : ι → Matrix ι ι F} (hc : PencilCyclic p) {M₁ M₂ M₃ : Matrix ι ι F}
    (h : PencilIso p p M₁ M₂ M₃) (h1 : IsUnit M₁.det) (h3 : IsUnit M₃.det) :
    PencilIso p p M₂ (M₃ᵀ)⁻¹ (M₁ᵀ)⁻¹ := by
  intro Y
  apply matrix_ext_dot
  intro X' Z
  have h3t : IsUnit M₃ᵀ.det := by rwa [det_transpose]
  set W := (M₃ᵀ)⁻¹ *ᵥ Z with hW
  set V := M₁⁻¹ *ᵥ X' with hV
  have hX' : X' = M₁ *ᵥ V := by
    rw [hV, mulVec_mulVec, mul_nonsing_inv _ h1, one_mulVec]
  have hMW : M₃ᵀ *ᵥ W = Z := by
    rw [hW, mulVec_mulVec, mul_nonsing_inv _ h3t, one_mulVec]
  have step1 : X' ⬝ᵥ ((pen p (M₂ *ᵥ Y) * (M₃ᵀ)⁻¹) *ᵥ Z) = W ⬝ᵥ (pen p X' *ᵥ (M₂ *ᵥ Y)) := by
    rw [← mulVec_mulVec, ← hW, hc X' (M₂ *ᵥ Y) W]
  have step2 : pen p X' *ᵥ (M₂ *ᵥ Y) = M₃ *ᵥ (pen p V *ᵥ Y) := by
    rw [hX', mulVec_mulVec, h V, ← mulVec_mulVec]
  have step3 : W ⬝ᵥ (M₃ *ᵥ (pen p V *ᵥ Y)) = Z ⬝ᵥ (pen p V *ᵥ Y) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMW]
  have step4 : V ⬝ᵥ (pen p Y *ᵥ Z) = X' ⬝ᵥ (((M₁ᵀ)⁻¹ * pen p Y) *ᵥ Z) := by
    rw [← mulVec_mulVec, dotProduct_mulVec X', ← mulVec_transpose, transpose_nonsing_inv,
      transpose_transpose, ← hV]
  rw [step1, step2, step3, hc V Y Z, step4]

end Monomial

end Semifields
