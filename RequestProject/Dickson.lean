import RequestProject.FamilyPencil
import RequestProject.Linearized

/-!
# Dickson matrices and the pencil form of an isotopism

Let `τ₁, τ₂` generate the cyclic Galois group of `F / K` (of order `n`).  For a `K`-linear map
`T` of `F`, a (mixed) *Dickson matrix* is a matrix `D` over `F` with
`D Φ_{τ₁}(x) = Φ_{τ₂}(T x)`, where `Φ_τ(x) = (τ^i x)_i` are the conjugate coordinates
(`eq:dickson`).  Such a matrix exists, is unique and is invertible when `T` is.

A `K`-linear isotopism between two multiplications whose split pencils are known is turned
into a pencil isotopy `L_Q(D_A X) D_B = D_C L_P(X)` (`eq:pencilisotopy`).  We do this for an
isotopism between two members of the family (possibly written with different generators) and
for an isotopism from a member of the family to a generalized twisted field.
-/

namespace Semifields

open scoped BigOperators
open Matrix

section Dickson

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n]

/-- `D` is a Dickson matrix of `T` from `τ₁`-coordinates to `τ₂`-coordinates. -/
def IsDickson (τ₁ τ₂ : F ≃ₐ[K] F) (T : F → F) (D : Matrix (ZMod n) (ZMod n) F) : Prop :=
  ∀ x, D *ᵥ Phi n τ₁ x = Phi n τ₂ (T x)

/-- Dickson matrices exist. -/
theorem exists_dickson [FiniteDimensional K F] {τ₁ : F ≃ₐ[K] F}
    (hinj : Function.Injective (fun i : ZMod n => sig τ₁ i)) (hfin : Module.finrank K F = n)
    (τ₂ : F ≃ₐ[K] F) (T : F →ₗ[K] F) : ∃ D : Matrix (ZMod n) (ZMod n) F, IsDickson τ₁ τ₂ T D := by
  have : ∀ i : ZMod n, ∃ d : ZMod n → F, ∀ x, sig τ₂ i (T x) = ∑ k, d k * sig τ₁ k x :=
    fun i => by
      obtain ⟨d, hd⟩ := exists_sig_expansion hinj hfin ((sig τ₂ i).toLinearMap ∘ₗ T)
      exact ⟨d, fun x => by simpa using hd x⟩
  choose d hd using this
  refine ⟨Matrix.of fun i k => d i k, fun x => ?_⟩
  funext i
  simp [mulVec, dotProduct, Phi, hd]

/-- Two matrices agreeing on all conjugate-coordinate vectors are equal. -/
theorem eq_of_mulVec_Phi {τ₁ : F ≃ₐ[K] F} (hinj : Function.Injective (fun i : ZMod n => sig τ₁ i))
    {M M' : Matrix (ZMod n) (ZMod n) F}
    (h : ∀ y, M *ᵥ Phi n τ₁ y = M' *ᵥ Phi n τ₁ y) : M = M' := by
  ext i k
  have hc := sig_coeff_eq_zero hinj (fun k => M i k - M' i k) (fun y => by
    have := congrFun (h y) i
    simp only [mulVec, dotProduct, Phi] at this
    simp [sub_mul, Finset.sum_sub_distrib, this])
  exact sub_eq_zero.mp (hc k)

/-- A pencil vanishing at all conjugate-coordinate vectors is zero. -/
theorem pen_eq_zero_of_Phi {τ₁ : F ≃ₐ[K] F} (hinj : Function.Injective (fun i : ZMod n => sig τ₁ i))
    (p : ZMod n → Matrix (ZMod n) (ZMod n) F) (h : ∀ x, pen p (Phi n τ₁ x) = 0) : p = 0 := by
  funext k
  ext i j
  have hc := sig_coeff_eq_zero hinj (fun k => p k i j) (fun x => by
    have := congrArg (fun M => M i j) (h x)
    simpa [pen_self_apply, Phi, mul_comm] using this)
  simpa using hc k

/-- A pencil isotopy may be checked at conjugate-coordinate vectors. -/
theorem pencilIso_of_Phi {τ₁ : F ≃ₐ[K] F} (hinj : Function.Injective (fun i : ZMod n => sig τ₁ i))
    {pQ pP : ZMod n → Matrix (ZMod n) (ZMod n) F} {M₁ M₂ M₃ : Matrix (ZMod n) (ZMod n) F}
    (h : ∀ x, pen pQ (M₁ *ᵥ Phi n τ₁ x) * M₂ = M₃ * pen pP (Phi n τ₁ x)) :
    PencilIso pQ pP M₁ M₂ M₃ := by
  rw [pencilIso_iff]
  have hG := pen_eq_zero_of_Phi hinj
    (fun k => pen pQ (M₁ *ᵥ Pi.single k 1) * M₂ - M₃ * pP k) (fun x => by
      rw [← pencil_defect (R := F)]
      simp [h x])
  intro k
  exact sub_eq_zero.mp (congrFun hG k)

/-- The Dickson matrix of an invertible map is invertible. -/
theorem isUnit_det_of_isDickson [FiniteDimensional K F] {τ₁ τ₂ : F ≃ₐ[K] F}
    (hinj₁ : Function.Injective (fun i : ZMod n => sig τ₁ i))
    (hinj₂ : Function.Injective (fun i : ZMod n => sig τ₂ i)) (hfin : Module.finrank K F = n)
    {T : F ≃ₗ[K] F} {D : Matrix (ZMod n) (ZMod n) F} (hD : IsDickson τ₁ τ₂ T D) :
    IsUnit D.det := by
  obtain ⟨D', hD'⟩ := exists_dickson hinj₂ hfin τ₁ T.symm.toLinearMap
  have h : D' * D = 1 := eq_of_mulVec_Phi hinj₁ (fun y => by
    rw [← mulVec_mulVec, hD, hD', one_mulVec]
    simp)
  exact Matrix.isUnit_det_of_left_inverse h

/-- Row `0` of a Dickson matrix is the coefficient vector of the linearized polynomial. -/
lemma dickson_apply_eq {τ₁ τ₂ : F ≃ₐ[K] F} {T : F → F} {D : Matrix (ZMod n) (ZMod n) F}
    (hD : IsDickson τ₁ τ₂ T D) (x : F) : T x = ∑ k, D 0 k * sig τ₁ k x := by
  have := congrFun (hD x) 0
  simp only [mulVec, dotProduct, Phi, sig_zero] at this
  rw [this]
  rfl

/-- A map with a monomial Dickson matrix is a single linearized monomial. -/
theorem monomial_of_isDickson {τ₁ τ₂ : F ≃ₐ[K] F} {T : F → F} {D : Matrix (ZMod n) (ZMod n) F}
    (hD : IsDickson τ₁ τ₂ T D) (hmon : RowMonomial D) :
    ∃ a : F, a ≠ 0 ∧ ∃ i : ZMod n, ∀ x, T x = a * sig τ₁ i x := by
  obtain ⟨j, hj0, hj⟩ := hmon 0
  refine ⟨D 0 j, hj0, j, fun x => ?_⟩
  rw [dickson_apply_eq hD, Finset.sum_eq_single j]
  · intro k _ hk; rw [hj k hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Dickson

section Isotopisms

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n]

/-- **The pencil form of an isotopism between two members of the family**, written in the
conjugate coordinates of two generators `τ₁, τ₂`. -/
theorem pencilIso_famMul {τ₁ τ₂ : F ≃ₐ[K] F} (hτ₁ : τ₁ ^ n = 1) (hτ₂ : τ₂ ^ n = 1)
    (hinj₁ : Function.Injective (fun i : ZMod n => sig τ₁ i)) {w : K} {A B C : F → F}
    (hABC : ∀ x y, famMul n τ₂ w (A x) (B y) = C (famMul n τ₁ w x y))
    {DA DB DC : Matrix (ZMod n) (ZMod n) F} (hA : IsDickson τ₁ τ₂ A DA)
    (hB : IsDickson τ₁ τ₂ B DB) (hC : IsDickson τ₁ τ₂ C DC) :
    PencilIso (lwP (algebraMap K F w)) (lwP (algebraMap K F w)) DA DB DC := by
  apply pencilIso_of_Phi hinj₁
  intro x
  apply eq_of_mulVec_Phi hinj₁
  intro y
  rw [← mulVec_mulVec, ← mulVec_mulVec, hA, hB, pen_lwP_self, pen_lwP_self,
    LwM_mulVec_Phi hτ₂, hABC, ← hC, LwM_mulVec_Phi hτ₁]

/-- The split pencil of `x ∘ y = x y - c σ^α(x) σ^β(y)` computes the multiplication. -/
lemma gtfM_mulVec_Phi {σ : F ≃ₐ[K] F} (hσ : σ ^ n = 1) (c : F) (α β : ZMod n) (x y : F) :
    gtfM (fun i => sig σ i c) α β (Phi n σ x) *ᵥ Phi n σ y
      = Phi n σ (x * y - c * sig σ α x * sig σ β y) := by
  funext i
  rw [gtfM_mulVec]
  simp only [Phi, map_sub, map_mul, sig_add_apply hσ]

/-- **The pencil form of an isotopism from a member of the family to a generalized twisted
field** `x ∘ y = x y - c σ^α(x) σ^β(y)`. -/
theorem pencilIso_gtf {σ : F ≃ₐ[K] F} (hσ : σ ^ n = 1)
    (hinj : Function.Injective (fun i : ZMod n => sig σ i)) {w : K} {c : F} {α β : ZMod n}
    {A B C : F → F}
    (hABC : ∀ x y, A x * B y - c * sig σ α (A x) * sig σ β (B y) = C (famMul n σ w x y))
    {DA DB DC : Matrix (ZMod n) (ZMod n) F} (hA : IsDickson σ σ A DA)
    (hB : IsDickson σ σ B DB) (hC : IsDickson σ σ C DC) :
    PencilIso (gtfP (fun i => sig σ i c) α β) (lwP (algebraMap K F w)) DA DB DC := by
  apply pencilIso_of_Phi hinj
  intro x
  apply eq_of_mulVec_Phi hinj
  intro y
  rw [← mulVec_mulVec, ← mulVec_mulVec, hA, hB, pen_gtfP_self, pen_lwP_self,
    gtfM_mulVec_Phi hσ, hABC, ← hC, LwM_mulVec_Phi hσ]

end Isotopisms

end Semifields
