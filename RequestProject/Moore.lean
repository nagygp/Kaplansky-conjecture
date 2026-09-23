import RequestProject.Construction

/-!
# Moore matrices and the comparison of split and ordinary coordinates

This file proves the content of Lemma `lem:moore` of the paper in the form needed here.

If `b` is a `K`-basis of `F` and `σ` generates a cyclic group of `K`-automorphisms of `F` of
order `n`, the *Moore matrix* is `U i j = σ^i (b j)`.  It is invertible (Dedekind's
independence of characters).  If a matrix `D` over `F` satisfies
`D (σ^i x)_i = (σ^i (T x))_i` for a `K`-linear map `T`, then `D U = U M`, where `M` is the
matrix of `T` in the basis `b`.  In particular `det D = det T`.
-/

namespace Semifields

open scoped BigOperators
open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F}

/-- The Moore matrix `U i j = σ^i (b j)` of a `K`-basis `b` of `F`. -/
noncomputable def mooreMatrix (σ : F ≃ₐ[K] F) (b : Module.Basis (ZMod n) K F) :
    Matrix (ZMod n) (ZMod n) F :=
  Matrix.of fun i j => sig σ i (b j)

omit [NeZero n] in
@[simp] lemma mooreMatrix_apply (b : Module.Basis (ZMod n) K F) (i j : ZMod n) :
    mooreMatrix σ b i j = sig σ i (b j) := rfl

/-- Dedekind's independence of characters: the Moore matrix of a basis is invertible. -/
theorem det_mooreMatrix_ne_zero (hinj : Function.Injective (fun i : ZMod n => sig σ i))
    (b : Module.Basis (ZMod n) K F) : (mooreMatrix σ b).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hb : ∀ j : ZMod n, ∑ i : ZMod n, c i * sig σ i (b j) = 0 := by
    intro j
    have := congrFun hc j
    simpa [Matrix.vecMul, dotProduct, mooreMatrix] using this
  have hphi : (∑ i : ZMod n, (LinearMap.mulLeft K (c i)) ∘ₗ ((sig σ i).toLinearMap)) = 0 := by
    apply Module.Basis.ext b
    intro j
    simpa using hb j
  have hzero : ∀ y : F, ∑ i : ZMod n, c i * sig σ i y = 0 := by
    intro y
    have := congrArg (fun f : F →ₗ[K] F => f y) hphi
    simpa using this
  -- this contradicts linear independence of distinct monoid homomorphisms
  have hmh : Function.Injective (fun i : ZMod n => ((sig σ i : F ≃ₐ[K] F) : F →* F)) := by
    intro i j hij
    refine hinj ?_
    exact AlgEquiv.ext fun x => congrFun (congrArg (fun f : F →* F => (f : F → F)) hij) x
  have hli := (linearIndependent_monoidHom F F).comp _ hmh
  have := Fintype.linearIndependent_iff.mp hli c (by
    funext y
    simpa using hzero y)
  exact hc0 (funext this)

/-- Lemma `lem:moore`: a Dickson-type matrix `D` for a `K`-linear map `T` is conjugate, by the
Moore matrix, to the matrix of `T` in the basis. -/
theorem dickson_mul_moore (b : Module.Basis (ZMod n) K F) (T : F →ₗ[K] F)
    (D : Matrix (ZMod n) (ZMod n) F)
    (hD : ∀ y : F, D.mulVec (Phi n σ y) = Phi n σ (T y)) :
    D * mooreMatrix σ b
      = mooreMatrix σ b * ((LinearMap.toMatrix b b T).map (algebraMap K F)) := by
  ext i j
  have hleft : (D * mooreMatrix σ b) i j = sig σ i (T (b j)) := by
    have := congrFun (hD (b j)) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Phi, mooreMatrix] using this
  rw [hleft, Matrix.mul_apply]
  have hTb : T (b j) = ∑ k : ZMod n, (LinearMap.toMatrix b b T) k j • b k := by
    conv_lhs => rw [← b.sum_repr (T (b j))]
    simp [LinearMap.toMatrix_apply]
  rw [hTb, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.smul_def, map_mul, sig_algebraMap]
  simp [mooreMatrix, mul_comm]

/-- The determinant of a Dickson-type matrix is the determinant of the corresponding
`K`-linear map. -/
theorem det_eq_of_dickson (hinj : Function.Injective (fun i : ZMod n => sig σ i))
    (b : Module.Basis (ZMod n) K F) (T : F →ₗ[K] F) (D : Matrix (ZMod n) (ZMod n) F)
    (hD : ∀ y : F, D.mulVec (Phi n σ y) = Phi n σ (T y)) :
    D.det = algebraMap K F (LinearMap.det T) := by
  have hU := det_mooreMatrix_ne_zero hinj b
  have h := congrArg Matrix.det (dickson_mul_moore b T D hD)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hdet : D.det * (mooreMatrix σ b).det
      = ((LinearMap.toMatrix b b T).map (algebraMap K F)).det * (mooreMatrix σ b).det := by
    rw [h]; ring
  have hcancel := mul_right_cancel₀ hU hdet
  rw [hcancel, show (((LinearMap.toMatrix b b) T).map (algebraMap K F : K → F))
      = (algebraMap K F).mapMatrix ((LinearMap.toMatrix b b) T) from rfl, ← RingHom.map_det]
  congr 1
  rw [← LinearMap.det_toMatrix b T]



section OrdinaryDeterminant

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

/-- A `K`-basis of `F` indexed by `ZMod n`, when `σ` runs over the whole Galois group. -/
noncomputable def basisZMod (hbij : Function.Bijective (fun i : ZMod n => sig σ i)) :
    Module.Basis (ZMod n) K F := by
  have hcard : Module.finrank K F = n := by
    have h1 : Nat.card (F ≃ₐ[K] F) = Module.finrank K F := IsGalois.card_aut_eq_finrank K F
    have h2 : Nat.card (F ≃ₐ[K] F) = n := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_of_bijective hbij, ZMod.card]
    omega
  exact (Module.finBasisOfFinrankEq K F hcard).reindex
    (Fintype.equivFinOfCardEq (ZMod.card n)).symm

/-- The product of the conjugates of `x` is its norm. -/
lemma prod_sig_eq_norm (hbij : Function.Bijective (fun i : ZMod n => sig σ i)) (x : F) :
    ∏ i : ZMod n, sig σ i x = algebraMap K F (Algebra.norm K x) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_bijective _ hbij _ _ (fun _ => rfl)

/-- **`thm:division`, ordinary-coordinate determinant.**  The determinant of the `K`-linear
map `y ↦ x * y` of the family is `λ_n(w) · N_{F/K}(x)`. -/
theorem det_famMul_left (hbij : Function.Bijective (fun i : ZMod n => sig σ i))
    (hσ : σ ^ n = 1) (hw : w ^ 2 - w + 1 = 0) (hodd : Odd n) (h3 : 3 ≤ n) (x : F) :
    LinearMap.det (famMulₗ n σ w x) = lam w n * Algebra.norm K x := by
  have hinj : Function.Injective (fun i : ZMod n => sig σ i) := hbij.1
  set b := basisZMod (σ := σ) (n := n) hbij with hb
  have hD : ∀ y : F, (LwM (algebraMap K F w) (Phi n σ x)).mulVec (Phi n σ y)
      = Phi n σ (famMulₗ n σ w x y) := fun y => LwM_mulVec_Phi hσ w x y
  have hdet := det_eq_of_dickson hinj b (famMulₗ n σ w x) _ hD
  rcases eq_or_ne x 0 with rfl | hx
  · have hzero : famMulₗ n σ w 0 = 0 := by
      ext y
      simp
    rw [hzero, Algebra.norm_zero, mul_zero]
    rw [LinearMap.det_zero' b]
  · have hsplit := det_LwM_Phi (σ := σ) hw hodd h3 hx
    rw [hsplit] at hdet
    have : algebraMap K F (LinearMap.det (famMulₗ n σ w x))
        = algebraMap K F (lam w n * Algebra.norm K x) := by
      rw [← hdet, map_mul]
      congr 1
      simpa [Phi] using prod_sig_eq_norm hbij x
    exact (algebraMap K F).injective this

end OrdinaryDeterminant

end Semifields
