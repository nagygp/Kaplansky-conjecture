import RequestProject.Parameters
import RequestProject.Nonisotopy

/-!
# Exclusion of the Albert generalized twisted fields (`thm:nonisotopy`, prime dimension)

Let `n ≥ 5` be prime.  Every automorphism of `F / K` is a power of the generator `σ`, so an
Albert generalized twisted field on `F` has the form `x ∘ y = x y - c σ^α(x) σ^β(y)`.  We show
that no member of the family is `K`-linearly isotopic to such a multiplication, for every
`c ∈ F` and all `α, β` (this includes the field multiplication, `c = 0`).

If `β = 0` the multiplication `(x - c σ^α(x)) y` is isotopic to the field, which is excluded by
the idealiser argument.  If `β ≠ 0`, its split left determinant is `(1 - N(c)) ∏ X_i`, so by
the monomial lemma the first map of an isotopism is a linearized monomial; evaluating the
pencil identity at the determinant vertex `e_0` compares the rank four of `L_w(e_0)`
(`eq:rank-four`) with rank at most two for the twisted field (its vertex rank), a
contradiction.  This is the determinant-vertex-rank argument of the paper.
-/

namespace Semifields

open scoped BigOperators
open Matrix

section GTF

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n]

omit [Fintype K] [Fintype F] [FiniteDimensional K F] [IsGalois K F] in
/-- The Dickson matrix of a linearized monomial `x ↦ a σ^i(x)`. -/
lemma isDickson_monomial {σ : F ≃ₐ[K] F} (hσ : σ ^ n = 1) (a : F) (i : ZMod n) :
    IsDickson σ σ (fun x => a * sig σ i x) (shiftM i (fun r => sig σ r a)) := by
  intro x
  funext r
  rw [shiftM_mulVec]
  simp only [Phi, map_mul, sig_add_apply hσ]

omit [Fintype K] [Fintype F] [FiniteDimensional K F] [IsGalois K F] [Algebra K F] in
lemma shiftM_mulVec_single (i : ZMod n) (t : ZMod n → F) :
    shiftM i t *ᵥ Pi.single 0 1 = Pi.single (-i) (t (-i)) := by
  funext r
  rw [shiftM_mulVec]
  by_cases hr : r = -i
  · subst hr; rw [neg_add_cancel]; simp
  · have : r + i ≠ 0 := fun h => hr (eq_neg_of_add_eq_zero_left h)
    simp [this, hr]

/-- **No member of the family is `K`-linearly isotopic to a generalized twisted field**
`x ∘ y = x y - c σ^α(x) σ^β(y)`, in prime dimension `n ≥ 5`. -/
theorem not_isotopicLin_gtf (hn : n.Prime) (hn5 : 5 ≤ n) (hq : Fintype.card K % 3 = 1)
    {σ : F ≃ₐ[K] F} (hσgen : Function.Bijective (fun i : ZMod n => sig σ i)) {w : K}
    (hw : w ^ 2 - w + 1 = 0) (c : F) (α β : ZMod n) :
    ¬ IsotopicLin K (famMul n σ w) (fun x y => x * y - c * sig σ α x * sig σ β y) := by
  rintro ⟨A, B, C, hABC⟩
  haveI := Fact.mk hn
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod_three hq
  have hmod : n % 6 = 1 ∨ n % 6 = 5 := by
    have h2 : ¬ 2 ∣ n := fun h => by
      rcases (Nat.dvd_prime hn).mp h with h | h <;> omega
    have h3' : ¬ 3 ∣ n := fun h => by
      rcases (Nat.dvd_prime hn).mp h with h | h <;> omega
    omega
  have hodd : Odd n := by rcases hmod with h | h <;> exact ⟨n / 2, by omega⟩
  have hσ := pow_eq_one_of_bij hσgen
  have hfin := finrank_of_bij hσgen
  by_cases hβ : β = 0
  · -- the multiplication factors through `x ↦ x - c σ^α(x)` and is isotopic to the field
    subst hβ
    have hQ0 : ∀ x' y', x' * y' - c * sig σ α x' * sig σ (0 : ZMod n) y' = 0 →
        x' = 0 ∨ y' = 0 := by
      intro x' y' h0
      have h1 := hABC (A.symm x') (B.symm y')
      simp only [LinearEquiv.apply_symm_apply] at h1
      rw [h0] at h1
      have h2 : famMul n σ w (A.symm x') (B.symm y') = 0 := by
        have := congrArg C.symm h1
        simpa using this.symm
      rcases famMul_eq_zero_iff hσ hw h3 hmod hn5 h2 with h | h
      · left; simpa using congrArg A h
      · right; simpa using congrArg B h
    let φ : F →+ F :=
      { toFun := fun x => x - c * sig σ α x
        map_zero' := by simp
        map_add' := fun x y => by simp only [map_add]; ring }
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      rcases hQ0 x 1 (by simpa [φ] using hx) with h | h
      · exact h
      · exact absurd h one_ne_zero
    have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφinj
    let φe : F ≃+ F := AddEquiv.ofBijective φ hφbij
    refine not_isotopic_field hq hn5 ?_ hσgen hw ⟨A.toAddEquiv.trans φe, B.toAddEquiv,
      C.toAddEquiv, fun x y => ?_⟩
    · rw [Nat.gcd_comm, Nat.gcd_rec]
      rcases hmod with h | h <;> rw [h] <;> norm_num
    · have := hABC x y
      simp only [sig_zero, AlgEquiv.one_apply] at this
      simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, φe,
        AddEquiv.ofBijective_apply, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [sub_mul]
      exact this
  · -- the vertex-rank argument
    have hβu : IsUnit β := isUnit_iff_ne_zero.mpr hβ
    obtain ⟨DA, hDA⟩ := exists_dickson hσgen.1 hfin σ A.toLinearMap
    obtain ⟨DB, hDB⟩ := exists_dickson hσgen.1 hfin σ B.toLinearMap
    obtain ⟨DC, hDC⟩ := exists_dickson hσgen.1 hfin σ C.toLinearMap
    have uC := isUnit_det_of_isDickson hσgen.1 hσgen.1 hfin (T := C) hDC
    have hiso := pencilIso_gtf hσ hσgen.1 (A := A) (B := B) (C := C) (c := c) (α := α)
      (β := β) (w := w) (fun x y => hABC x y) hDA hDB hDC
    set w' := algebraMap K F w with hw'def
    have hw' : w' ^ 2 - w' + 1 = 0 := by
      have := congrArg (algebraMap K F) hw
      simpa [hw'def] using this
    have hw'0 : w' ≠ 0 := by
      intro h0; rw [h0] at hw'; norm_num at hw'
    set lamF : F := (1 + w' ^ n) ^ 2 * (1 - w' ^ (2 * n)) with hlamF
    have hlam0 : lamF ≠ 0 := by
      have hl := lam_ne_zero hw h3 hmod
      have : lamF = algebraMap K F (lam w n) := by simp [hlamF, lam, hw'def]
      rw [this]
      exact fun h0 => hl ((algebraMap K F).injective (by rw [h0, map_zero]))
    have hQ := det_pen_gtfP (fun i => sig σ i c) α hβu hβ hodd
    have hP := det_pen_lwP w' hw' hodd (by omega)
    have mA : RowMonomial DA :=
      rowMonomial_of_pencilIso hiso _ lamF hQ (hP _) hlam0 uC.ne_zero
    obtain ⟨a, ha, i, hA⟩ := monomial_of_isDickson hDA mA
    have hDA' : DA = shiftM i (fun r => sig σ r a) := by
      apply eq_of_mulVec_Phi hσgen.1
      intro y
      rw [hDA y, isDickson_monomial hσ a i y]
      exact congrArg (Phi n σ) (hA y)
    have hvert := hiso (Pi.single 0 1)
    rw [hDA', shiftM_mulVec_single, pen_gtfP_self, pen_lwP_self] at hvert
    have hrank := congrArg Matrix.rank hvert
    rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ uC] at hrank
    have h4 : (LwM w' (Pi.single (0 : ZMod n) (1 : F))).rank = 4 :=
      rank_LwM_coordPt (E := F) hn5 hw'0
    have hle := (Matrix.rank_mul_le_left
      (gtfM (fun i => sig σ i c) α β (Pi.single (-i) (sig σ (-i) a))) DB).trans
      (rank_gtfM_single_le _ α β (-i) _)
    omega

end GTF

end Semifields
