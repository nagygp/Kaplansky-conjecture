import RequestProject.MenichettiFamily

/-!
# Semilinearity of isotopisms (`lem:semilinearity`) and the Galois twist

Let `K ⊆ F` be finite fields.  If `(A, B, C)` is an (additive) isotopism from a `K`-bilinear
multiplication `*` to a `K`-bilinear multiplication `∘` without zero divisors, whose spread set
has left idealiser consisting of `K`-scalar maps only, then conjugation by `C` induces a ring
automorphism `θ` of `K`, and all three maps are `θ`-semilinear (`semilinear_of_isotopic`).
Every automorphism of `K` is a power `a ↦ a ^ (p ^ j)` of the Frobenius, and the same power
of the Frobenius of `F` extends it; composing with it gives a `K`-linear isotopism from the
*Galois twist* of `*` to `∘` (`isotopicLin_twist_of_isotopic`, `eq:semilinear-reduction`).

For the family this twist only changes the coefficient: `𝒫_{w,s}^{[j]} = 𝒫_{w^{p^j},s}`
(`famMul_twist`, `eq:familytwist`).
-/

namespace Semifields

open scoped BigOperators

/-- Every ring endomorphism of a finite field of characteristic `p` is a power of the
Frobenius. -/
theorem exists_frob_pow_eq {K : Type*} [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (θ : K →+* K) : ∃ j : ℕ, ∀ a : K, θ a = a ^ (p ^ j) := by
  letI := ZMod.algebra K p
  haveI := Fintype.ofFinite K
  have hbij : Function.Bijective θ := Finite.injective_iff_bijective.mp θ.injective
  let θe : K ≃+* K := RingEquiv.ofBijective θ hbij
  let θa : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := θe) (fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((θe : K →+* K).comp (algebraMap (ZMod p) K))
      (algebraMap (ZMod p) K)) x)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) K).2 θa
  refine ⟨n.1, fun a => ?_⟩
  have h1 : θ a = θa a := rfl
  rw [h1, ← hn]
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

section Semilinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Semilinearity of isotopisms** (`lem:semilinearity`, in the form used for the family).
Let `(A, B, C)` be an additive isotopism from `mulP` to `mulQ`, both `K`-bilinear, where `mulQ`
has no zero divisors and the left idealiser of its spread set consists of `K`-scalar maps.
Then there is a ring endomorphism `θ` of `K` for which `A`, `B` and `C` are all
`θ`-semilinear. -/
theorem semilinear_of_isotopic {mulP mulQ : F → F → F}
    (haddQ : ∀ y, ∀ x₁ x₂, mulQ (x₁ + x₂) y = mulQ x₁ y + mulQ x₂ y)
    (haddQ' : ∀ x, ∀ y₁ y₂, mulQ x (y₁ + y₂) = mulQ x y₁ + mulQ x y₂)
    (hPl : ∀ (a : K) x y, mulP (algebraMap K F a * x) y = algebraMap K F a * mulP x y)
    (hPr : ∀ (a : K) x y, mulP x (algebraMap K F a * y) = algebraMap K F a * mulP x y)
    (hQl : ∀ (a : K) x y, mulQ (algebraMap K F a * x) y = algebraMap K F a * mulQ x y)
    (hQr : ∀ (a : K) x y, mulQ x (algebraMap K F a * y) = algebraMap K F a * mulQ x y)
    (hQ0 : ∀ x y, mulQ x y = 0 → x = 0 ∨ y = 0)
    (hQid : leftIdealiser (spreadSet mulQ haddQ) ⊆ scalarMaps K F)
    {A B C : F ≃+ F} (h : ∀ x y, mulQ (A x) (B y) = C (mulP x y)) :
    ∃ θ : K →+* K, ∀ (a : K) (x : F),
      A (algebraMap K F a * x) = algebraMap K F (θ a) * A x ∧
      B (algebraMap K F a * x) = algebraMap K F (θ a) * B x ∧
      C (algebraMap K F a * x) = algebraMap K F (θ a) * C x := by
  -- conjugates of the scalar maps lie in the left idealiser of `mulQ`
  have hmem : ∀ a : K, ∃ b : K, ∀ z : F,
      C (algebraMap K F a * C.symm z) = algebraMap K F b * z := by
    intro a
    let T : F →+ F := C.toAddMonoidHom.comp
      ((AddMonoidHom.mulLeft (algebraMap K F a)).comp C.symm.toAddMonoidHom)
    have hT : T ∈ leftIdealiser (spreadSet mulQ haddQ) := by
      rw [mem_leftIdealiser_spreadSet_iff]
      intro y
      refine ⟨B (algebraMap K F a * B.symm y), fun x => ?_⟩
      have e1 := h (A.symm x) (B.symm y)
      have e2 := h (A.symm x) (algebraMap K F a * B.symm y)
      simp only [AddEquiv.apply_symm_apply] at e1 e2
      simp only [T, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddMonoidHom.coe_mulLeft]
      rw [e1, AddEquiv.symm_apply_apply, e2, hPr]
    obtain ⟨b, hb⟩ := hQid hT
    exact ⟨b, fun z => hb z⟩
  choose θf hθf using hmem
  have hC : ∀ (a : K) (x : F), C (algebraMap K F a * x) = algebraMap K F (θf a) * C x := by
    intro a x
    have := hθf a (C x)
    rwa [AddEquiv.symm_apply_apply] at this
  have hθ1 : ∀ a : K, algebraMap K F (θf a) = C (algebraMap K F a * C.symm 1) := by
    intro a
    rw [hC, AddEquiv.apply_symm_apply, mul_one]
  have hinj : Function.Injective (algebraMap K F) := (algebraMap K F).injective
  let θ : K →+* K :=
    { toFun := θf
      map_one' := hinj (by rw [hθ1, map_one, one_mul, AddEquiv.apply_symm_apply])
      map_mul' := fun a b => hinj (by
        rw [hθ1, (algebraMap K F).map_mul, mul_assoc, hC, ← hθ1, (algebraMap K F).map_mul])
      map_zero' := hinj (by rw [hθ1, map_zero, zero_mul, map_zero])
      map_add' := fun a b => hinj (by rw [hθ1, map_add, add_mul, map_add, ← hθ1, ← hθ1,
          map_add]) }
  have hQsubl : ∀ u v w, mulQ (u - v) w = mulQ u w - mulQ v w := fun u v w =>
    (AddMonoidHom.mk' (fun u => mulQ u w) (haddQ w)).map_sub u v
  have hQsubr : ∀ u v w, mulQ w (u - v) = mulQ w u - mulQ w v := fun u v w =>
    (AddMonoidHom.mk' (fun u => mulQ w u) (haddQ' w)).map_sub u v
  refine ⟨θ, fun a x => ⟨?_, ?_, hC a x⟩⟩
  · have e := h (algebraMap K F a * x) (B.symm 1)
    rw [hPl, hC, ← h, AddEquiv.apply_symm_apply, ← hQl] at e
    have e' : mulQ (A (algebraMap K F a * x) - algebraMap K F (θf a) * A x) 1 = 0 := by
      rw [hQsubl, e, sub_self]
    rcases hQ0 _ _ e' with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 one_ne_zero
  · have e := h (A.symm 1) (algebraMap K F a * x)
    rw [hPr, hC, ← h, AddEquiv.apply_symm_apply, ← hQr] at e
    have e' : mulQ 1 (B (algebraMap K F a * x) - algebraMap K F (θf a) * B x) = 0 := by
      rw [hQsubr, e, sub_self]
    rcases hQ0 _ _ e' with h0 | h0
    · exact absurd h0 one_ne_zero
    · exact sub_eq_zero.mp h0

end Semilinear

section IsotopicLin

variable {K : Type*} [Field K] {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  [Module K V] [Module K W] [Module K U]

lemma IsotopicLin.symm {mulP : V → V → V} {mulQ : W → W → W} (h : IsotopicLin K mulP mulQ) :
    IsotopicLin K mulQ mulP := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨A.symm, B.symm, C.symm, fun x y => ?_⟩
  have := h (A.symm x) (B.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  rw [this, LinearEquiv.symm_apply_apply]

lemma IsotopicLin.trans {mulP : V → V → V} {mulQ : W → W → W} {mulR : U → U → U}
    (h₁ : IsotopicLin K mulP mulQ) (h₂ : IsotopicLin K mulQ mulR) : IsotopicLin K mulP mulR := by
  obtain ⟨A₁, B₁, C₁, h₁⟩ := h₁
  obtain ⟨A₂, B₂, C₂, h₂⟩ := h₂
  refine ⟨A₁.trans A₂, B₁.trans B₂, C₁.trans C₂, fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [h₂, h₁]

end IsotopicLin

section Twist

variable {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] (p : ℕ) [Fact p.Prime]
  [CharP F p]

/-- The Galois twist `x *^{[j]} y = φ (φ⁻¹ x * φ⁻¹ y)` of a multiplication by the power
`φ (x) = x ^ (p ^ j)` of the Frobenius (`eq:galois-twist`). -/
noncomputable def twistMul (j : ℕ) (mul : F → F → F) (x y : F) : F :=
  iterateFrobeniusEquiv F p j (mul ((iterateFrobeniusEquiv F p j).symm x)
    ((iterateFrobeniusEquiv F p j).symm y))

omit [Algebra K F] in
lemma iterateFrobeniusEquiv_apply' (j : ℕ) (x : F) : iterateFrobeniusEquiv F p j x = x ^ p ^ j := by
  rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]

variable {p}

/-- **The semilinear reduction** `eq:semilinear-reduction`: under the hypotheses of
`semilinear_of_isotopic`, some Galois twist of `mulP` is `K`-linearly isotopic to `mulQ`. -/
theorem isotopicLin_twist_of_isotopic [Finite K] {mulP mulQ : F → F → F}
    (haddQ : ∀ y, ∀ x₁ x₂, mulQ (x₁ + x₂) y = mulQ x₁ y + mulQ x₂ y)
    (haddQ' : ∀ x, ∀ y₁ y₂, mulQ x (y₁ + y₂) = mulQ x y₁ + mulQ x y₂)
    (hPl : ∀ (a : K) x y, mulP (algebraMap K F a * x) y = algebraMap K F a * mulP x y)
    (hPr : ∀ (a : K) x y, mulP x (algebraMap K F a * y) = algebraMap K F a * mulP x y)
    (hQl : ∀ (a : K) x y, mulQ (algebraMap K F a * x) y = algebraMap K F a * mulQ x y)
    (hQr : ∀ (a : K) x y, mulQ x (algebraMap K F a * y) = algebraMap K F a * mulQ x y)
    (hQ0 : ∀ x y, mulQ x y = 0 → x = 0 ∨ y = 0)
    (hQid : leftIdealiser (spreadSet mulQ haddQ) ⊆ scalarMaps K F)
    (h : Isotopic mulP mulQ) : ∃ j : ℕ, IsotopicLin K (twistMul p j mulP) mulQ := by
  haveI : CharP K p := (RingHom.charP_iff (algebraMap K F) (algebraMap K F).injective p).mpr
    inferInstance
  obtain ⟨A, B, C, hABC⟩ := h
  obtain ⟨θ, hθ⟩ := semilinear_of_isotopic haddQ haddQ' hPl hPr hQl hQr hQ0 hQid hABC
  obtain ⟨j, hj⟩ := exists_frob_pow_eq p θ
  refine ⟨j, ?_⟩
  set ψ := iterateFrobeniusEquiv F p j with hψ
  have hθsurj : Function.Surjective θ :=
    (Finite.injective_iff_bijective.mp θ.injective).2
  -- `ψ⁻¹` maps `K` to itself, inverting `θ`
  have hψK : ∀ k : K, ∃ b : K, θ b = k ∧ ψ.symm (algebraMap K F k) = algebraMap K F b := by
    intro k
    obtain ⟨b, hb⟩ := hθsurj k
    refine ⟨b, hb, ?_⟩
    rw [RingEquiv.symm_apply_eq, hψ, iterateFrobeniusEquiv_apply', ← map_pow, ← hj, hb]
  have hlin : ∀ (D : F ≃+ F), (∀ (a : K) (x : F),
      D (algebraMap K F a * x) = algebraMap K F (θ a) * D x) →
      ∀ (k : K) (x : F), D (ψ.symm (algebraMap K F k * x)) = algebraMap K F k * D (ψ.symm x) := by
    intro D hD k x
    obtain ⟨b, hb, hbk⟩ := hψK k
    rw [map_mul, hbk, hD, hb]
  let mk : (D : F ≃+ F) → (∀ (a : K) (x : F),
      D (algebraMap K F a * x) = algebraMap K F (θ a) * D x) → (F ≃ₗ[K] F) := fun D hD =>
    { toFun := fun x => D (ψ.symm x)
      invFun := fun x => ψ (D.symm x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun k x => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact hlin D hD k x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  refine ⟨mk A (fun a x => (hθ a x).1), mk B (fun a x => (hθ a x).2.1),
    mk C (fun a x => (hθ a x).2.2), fun x y => ?_⟩
  simp only [mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, twistMul]
  rw [hABC, ← hψ, RingEquiv.symm_apply_apply]

end Twist

section FamilyTwist

variable {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {p : ℕ} [Fact p.Prime]
  [CharP F p] {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F}

/-- **The Galois twist of the family** (`eq:familytwist`): `𝒫_{w,s}^{[j]} = 𝒫_{w^{p^j},s}`. -/
theorem twistMul_famMul (j : ℕ) (w : K) :
    twistMul p j (famMul n σ w) = famMul n σ (w ^ p ^ j) := by
  funext x y
  set ψ := iterateFrobeniusEquiv F p j with hψ
  have hcomm : ∀ (i : ZMod n) (u : F), ψ (sig σ i u) = sig σ i (ψ u) := by
    intro i u
    rw [hψ, iterateFrobeniusEquiv_apply', iterateFrobeniusEquiv_apply', map_pow]
  have hw : ψ (algebraMap K F w) = algebraMap K F (w ^ p ^ j) := by
    rw [hψ, iterateFrobeniusEquiv_apply', map_pow]
  simp only [twistMul, famMul, ← hψ, map_add, map_mul, hcomm, hw, RingEquiv.apply_symm_apply]

end FamilyTwist

section Opposite

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F}

/-- The identity `f_{w,-s}(x, y) = w f_{w^{-1},s}(x, y)` of `eq:opposite`; here
`w⁻¹ = 1 - w`, and the generator `σ^{-1}` is written `sig σ (-1)`. -/
theorem famMul_neg_one (hσ : σ ^ n = 1) {w : K} (hw : w ^ 2 - w + 1 = 0) (x y : F) :
    famMul n (sig σ (-1 : ZMod n)) w x y = algebraMap K F w * famMul n σ (1 - w) x y := by
  simp only [famMul, sig_sig hσ]
  rw [show (-1 : ZMod n) * 1 = -1 by ring, show (-1 : ZMod n) * 2 = -2 by ring,
    show (-1 : ZMod n) * -1 = 1 by ring, show (-1 : ZMod n) * -2 = 2 by ring, map_sub, map_one]
  have hW : algebraMap K F w ^ 2 - algebraMap K F w + 1 = 0 := by
    have := congrArg (algebraMap K F) hw
    simpa using this
  linear_combination (sig σ (2 : ZMod n) x * sig σ (1 : ZMod n) y
    + sig σ (-1 : ZMod n) x * sig σ (1 : ZMod n) y
    + sig σ (-1 : ZMod n) x * sig σ (-2 : ZMod n) y) * hW

/-- `𝒫_{w^{-1},s}` and `𝒫_{w,-s}` are `K`-linearly isotopic. -/
theorem isotopicLin_famMul_neg_one (hσ : σ ^ n = 1) {w : K} (hw : w ^ 2 - w + 1 = 0) :
    IsotopicLin K (famMul n σ (1 - w)) (famMul n (sig σ (-1 : ZMod n)) w) := by
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  refine ⟨LinearEquiv.refl K F, LinearEquiv.refl K F, LinearEquiv.smulOfNeZero K F w hw0,
    fun x y => ?_⟩
  simp only [LinearEquiv.refl_apply, LinearEquiv.smulOfNeZero_apply, Algebra.smul_def]
  exact famMul_neg_one hσ hw x y

/-- Powers of a generator by units of `ZMod n` are again generators. -/
lemma bijective_sig_sig_unit [Fintype (F ≃ₐ[K] F)] (hσgen : Function.Bijective (fun i : ZMod n => sig σ i))
    (u : ZMod n) (hu : IsUnit u) :
    Function.Bijective (fun i : ZMod n => sig (sig σ u) i) := by
  have hσ : σ ^ n = 1 := pow_eq_one_of_bij hσgen
  obtain ⟨v, rfl⟩ := hu
  have : (fun i : ZMod n => sig (sig σ (v : ZMod n)) i)
      = (fun i : ZMod n => sig σ i) ∘ (fun i => (v : ZMod n) * i) := by
    funext i; exact sig_sig hσ _ _
  rw [this]
  refine hσgen.comp ⟨fun a b h => ?_, fun b => ⟨(↑v⁻¹ : ZMod n) * b, ?_⟩⟩
  · simpa using congrArg (fun x => (↑v⁻¹ : ZMod n) * x) h
  · simp [← mul_assoc]

end Opposite

end Semifields
