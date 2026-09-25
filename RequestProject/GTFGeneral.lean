import RequestProject.FamilyIsotopy
import RequestProject.GTFIdealiser

/-!
# No member of the family is isotopic to a generalized twisted field (general `q`)

Let `K = 𝔽_q` with `q = p^e ≡ 1 (mod 3)`, let `r ≥ 5` be prime and `F = 𝔽_{q^r}`.  We show that
no member of the family is isotopic, by an arbitrary additive isotopism, to a multiplication
`x ∘ y = x y - c τ(x) υ(y)` with `c ∈ F` and `τ, υ` arbitrary automorphisms of `F`
(`not_isotopic_gtf`).  This covers the field `F` itself and all Albert generalized twisted
fields of order `q^r`.

The proof follows the paper (`thm:nonisotopy`):

* if `c = 0`, `τ = 1`, `υ = 1` or `τ = υ`, the multiplication is isotopic to the field `F`,
  which is excluded by the idealiser argument (`not_isotopic_field`);
* otherwise, the left idealisers of the spread sets of the twisted field and of its dual are the
  scalar maps by the fixed fields of `υ` and of `τ` (`GTFIdealiser`); since these idealisers
  have `q` elements (they are conjugate to those of the family, `thm:direct-nuclei`), both fixed
  fields are `K`.  This replaces Albert's nuclear calculation in the paper.  Hence `τ` and `υ`
  fix `K` and the twisted field is `K`-bilinear;
* the semilinear reduction (`lem:semilinearity`) then gives a `K`-linear isotopism from a
  Galois twist `𝒫_{w^{p^j},s}` of the member to the twisted field, which is excluded by the
  determinant-vertex-rank argument (`not_isotopicLin_gtf`).
-/

namespace Semifields

open scoped BigOperators

section Helpers

variable {F : Type*} [Field F]

/-- Isotopy transports the absence of zero divisors. -/
lemma noZeroDiv_of_isotopic {mulP mulQ : F → F → F}
    (hP : ∀ x y, mulP x y = 0 → x = 0 ∨ y = 0) (h : Isotopic mulP mulQ) :
    ∀ x y, mulQ x y = 0 → x = 0 ∨ y = 0 := by
  obtain ⟨A, B, C, hABC⟩ := h
  intro u v huv
  have e := hABC (A.symm u) (B.symm v)
  simp only [AddEquiv.apply_symm_apply] at e
  rw [huv, eq_comm, map_eq_zero_iff C C.injective] at e
  rcases hP _ _ e with h | h
  · left; simpa using congrArg A h
  · right; simpa using congrArg B h

/-- The additive maps `m_a : z ↦ a z` with `a ∈ X` are as many as the elements of `X`. -/
lemma card_mulMaps (X : Set F) :
    Nat.card {T : F →+ F | ∃ a ∈ X, ∀ z, T z = a * z} = Nat.card X := by
  symm
  refine Nat.card_eq_of_bijective
    (fun a : X => (⟨AddMonoidHom.mulLeft (a : F), ⟨a, a.2, fun z => rfl⟩⟩ :
      {T : F →+ F | ∃ a ∈ X, ∀ z, T z = a * z})) ⟨fun a b h => ?_, fun T => ?_⟩
  · have := congrArg (fun T : {T : F →+ F | ∃ a ∈ X, ∀ z, T z = a * z} => (T : F →+ F) 1) h
    simp only [AddMonoidHom.coe_mulLeft, mul_one] at this
    exact Subtype.ext this
  · obtain ⟨T, a, ha, hT⟩ := T
    exact ⟨⟨a, ha⟩, Subtype.ext (AddMonoidHom.ext fun x => (hT x).symm)⟩

/-- In a finite field, a subfield with as many elements as `K` is the image of `K`. -/
lemma subfield_eq_range_of_card {K : Type*} [Field K] [Fintype K] [Algebra K F] [Finite F]
    (S : Subfield F) (hS : Nat.card S = Fintype.card K) :
    (S : Set F) = Set.range (algebraMap K F) := by
  classical
  haveI := Fintype.ofFinite F
  set q := Fintype.card K with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  set P : Polynomial F := Polynomial.X ^ q - Polynomial.X with hPdef
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq1
  have hPdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq F hq1
  set R := P.roots.toFinset with hR
  have hRcard : R.card ≤ q := by
    calc R.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hPdeg
  have hmemR : ∀ x : F, x ^ q = x → x ∈ R := by
    intro x hx
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hP0, hPdef]
    simp [hx]
  have hSR : (S : Set F).toFinset ⊆ R := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    apply hmemR
    haveI : Fintype S := Fintype.ofFinite S
    have hcS : Fintype.card S = q := by rw [← Nat.card_eq_fintype_card, hS]
    have := FiniteField.pow_card (⟨x, hx⟩ : S)
    rw [hcS] at this
    exact congrArg Subtype.val this
  have hScard : (S : Set F).toFinset.card = q := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hS
  have hSeq : (S : Set F).toFinset = R :=
    Finset.eq_of_subset_of_card_le hSR (by rw [hScard]; exact hRcard)
  have hKR : Set.range (algebraMap K F) ⊆ (S : Set F) := by
    rintro _ ⟨k, rfl⟩
    have : algebraMap K F k ∈ R := hmemR _ (by rw [← map_pow, FiniteField.pow_card])
    rw [← hSeq, Set.mem_toFinset] at this
    exact this
  refine (Set.eq_of_subset_of_card_le hKR ?_).symm
  have h1 : Fintype.card (S : Set F) = q := by rw [← Nat.card_eq_fintype_card]; exact hS
  have h2 : Fintype.card (Set.range (algebraMap K F)) = q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_range_of_injective (algebraMap K F).injective,
      Nat.card_eq_fintype_card]
  omega

end Helpers

section Frobenius

variable {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The Frobenius `x ↦ x ^ p` generates the automorphisms of `F` over the prime field. -/
lemma bijective_sig_frobenius :
    letI := ZMod.algebra F p
    haveI : NeZero (Module.finrank (ZMod p) F) := ⟨Module.finrank_pos.ne'⟩
    Function.Bijective (fun i : ZMod (Module.finrank (ZMod p) F) =>
      sig (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) i) := by
  letI := ZMod.algebra F p
  haveI : NeZero (Module.finrank (ZMod p) F) := ⟨Module.finrank_pos.ne'⟩
  set N := Module.finrank (ZMod p) F
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F
  have hb := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F
  refine ⟨fun i j hij => ?_, fun g => ?_⟩
  · simp only [sig] at hij
    have := hb.1 (a₁ := ⟨i.val, ZMod.val_lt i⟩) (a₂ := ⟨j.val, ZMod.val_lt j⟩) hij
    exact ZMod.val_injective _ (congrArg Fin.val this)
  · obtain ⟨m, hm⟩ := hb.2 g
    refine ⟨(m.1 : ZMod N), ?_⟩
    simp only [sig]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt m.2]
    exact hm

/-- Every ring automorphism of `F` is a power of the Frobenius. -/
lemma exists_sig_frobenius_eq (τ : F ≃+* F) :
    letI := ZMod.algebra F p
    haveI : NeZero (Module.finrank (ZMod p) F) := ⟨Module.finrank_pos.ne'⟩
    ∃ α : ZMod (Module.finrank (ZMod p) F), ∀ x,
      τ x = sig (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) α x := by
  letI := ZMod.algebra F p
  haveI : NeZero (Module.finrank (ZMod p) F) := ⟨Module.finrank_pos.ne'⟩
  let τa : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := τ) (fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((τ : F →+* F).comp (algebraMap (ZMod p) F))
      (algebraMap (ZMod p) F)) x)
  obtain ⟨α, hα⟩ := (bijective_sig_frobenius p).2 τa
  exact ⟨α, fun x => by simp only at hα; rw [hα]; rfl⟩

end Frobenius

section FixedField

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Finite F] [Algebra K F]
variable {K₀ : Type*} [Field K₀] [Algebra K₀ F] [FiniteDimensional K₀ F]
  {N : ℕ} [NeZero N] {φ : F ≃ₐ[K₀] F}

/-- If a multiplication `mulP` without zero divisors, whose spread set has a left idealiser with
`|K|` elements, is isotopic to the twisted field `x y - c φ^α(x) φ^β(y)` (nondegenerate
parameters, `φ` generating `Gal(F/K₀)` and every additive map `K₀`-linear), then the fixed
field of `φ^β` is `K`. -/
theorem fixed_eq_range_of_isotopic_gtf (hφb : Function.Bijective (fun i : ZMod N => sig φ i))
    (hφfin : Module.finrank K₀ F = N) (hφN : φ ^ N = 1)
    (hlin : ∀ (T : F →+ F) (k : K₀) (z : F), T (algebraMap K₀ F k * z) = algebraMap K₀ F k * T z)
    {c : F} {α β : ZMod N} (hc : c ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β)
    {mulP : F → F → F} (haddP : ∀ y, ∀ x₁ x₂, mulP (x₁ + x₂) y = mulP x₁ y + mulP x₂ y)
    (hP0 : ∀ x y, mulP x y = 0 → x = 0 ∨ y = 0)
    (hPcard : Nat.card (leftIdealiser (spreadSet mulP haddP)) = Fintype.card K)
    (h : Isotopic mulP (gtfMul φ c α β)) :
    {a : F | sig φ β a = a} = Set.range (algebraMap K F) := by
  have h0 := noZeroDiv_of_isotopic hP0 h
  obtain ⟨A, B, C, hABC⟩ := h
  have hI : leftIdealiser (spreadSet (gtfMul φ c α β) (fun y x₁ x₂ => gtfMul_add_left c α β x₁ x₂ y))
      = {T : F →+ F | ∃ a ∈ {a : F | sig φ β a = a}, ∀ z, T z = a * z} := by
    ext T
    constructor
    · intro hT
      obtain ⟨a, ha, hfix⟩ := gtf_leftIdealiser_subset hφb hφfin hφN hc hα hβ hαβ h0
        (hlin T) hT
      exact ⟨a, hfix, ha⟩
    · rintro ⟨a, hfix, ha⟩
      rw [mem_leftIdealiser_spreadSet_iff]
      intro y
      refine ⟨a * y, fun x => ?_⟩
      simp only [Set.mem_setOf_eq] at hfix
      rw [ha]
      simp only [gtfMul, map_mul, hfix]
      ring
  have hcard := card_leftIdealiser_eq (haddP := haddP)
    (haddS := fun y x₁ x₂ => gtfMul_add_left c α β x₁ x₂ y) hABC
  rw [hI, card_mulMaps, hPcard] at hcard
  let S : Subfield F := RingHom.eqLocusField ((sig φ β : F ≃ₐ[K₀] F) : F →+* F) (RingHom.id F)
  have hSX : (S : Set F) = {a : F | sig φ β a = a} := by
    ext x
    exact RingHom.mem_eqLocusField
  rw [← hSX]
  apply subfield_eq_range_of_card
  rw [← hcard]
  rfl

end FixedField

section Main

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  {r : ℕ} [NeZero r]

omit [NeZero r] in
lemma gcd_six_of_prime (hr : r.Prime) (hr5 : 5 ≤ r) : Nat.gcd r 6 = 1 := by
  have : Nat.Coprime r 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases r <;> first | omega | norm_num at hr
  exact this

/-- The additive bijection of a finite field given by an injective additive map. -/
noncomputable def addEquivOfInjective (f : F →+ F) (hf : Function.Injective f) : F ≃+ F :=
  AddEquiv.ofBijective f (Finite.injective_iff_bijective.mp hf)

/-- **No member of the family is isotopic to a generalized twisted field** (the second half of
`thm:nonisotopy`, prime dimension, general `q`).  For every `c ∈ F` and all automorphisms
`τ, υ` of `F`, the member `𝒫_{w,s}` is not isotopic to `x ∘ y = x y - c τ(x) υ(y)`.
The case `c = 0` is the field `F`. -/
theorem not_isotopic_gtf (hr : r.Prime) (hr5 : 5 ≤ r) (hq : Fintype.card K % 3 = 1)
    {σ : F ≃ₐ[K] F} (hσgen : Function.Bijective (fun i : ZMod r => sig σ i)) {w : K}
    (hw : w ^ 2 - w + 1 = 0) (c : F) (τ υ : F ≃+* F) :
    ¬ Isotopic (famMul r σ w) (fun x y : F => x * y - c * τ x * υ y) := by
  intro h
  obtain ⟨p, hchar⟩ := CharP.exists K
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : FiniteDimensional K F := Module.Finite.of_finite
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod_three hq
  have hr6 := gcd_six_of_prime hr hr5
  have hmod := mod_six_of_gcd_six hr6
  have hσ : σ ^ r = 1 := pow_eq_one_of_bij hσgen
  have hP := isPresemifield_famMul hσ hw h3 hmod hr5
  have hfield := not_isotopic_field hq hr5 hr6 hσgen hw
  set G : F → F → F := fun x y => x * y - c * τ x * υ y with hG
  have h0 : ∀ x y, G x y = 0 → x = 0 ∨ y = 0 := noZeroDiv_of_isotopic hP.eq_zero_or_eq_zero h
  -- degenerate cases: `G` is isotopic to the field `F`
  by_cases hc : c = 0
  · apply hfield
    have : G = fun x y : F => x * y := by funext x y; simp [hG, hc]
    rwa [← this]
  by_cases hυ : ∀ x, υ x = x
  · apply hfield
    let D : F →+ F := AddMonoidHom.mk' (fun x => x - c * τ x) (fun a b => by
      simp only [map_add]; ring)
    have hDinj : Function.Injective D := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have : G x 1 = 0 := by
        simp only [hG, map_one, mul_one]
        exact hx
      rcases h0 x 1 this with h1 | h1
      · exact h1
      · exact absurd h1 one_ne_zero
    refine h.trans ⟨addEquivOfInjective D hDinj, AddEquiv.refl F, AddEquiv.refl F,
      fun x y => ?_⟩
    simp only [addEquivOfInjective, AddEquiv.ofBijective_apply, AddEquiv.refl_apply, D,
      AddMonoidHom.mk'_apply, hG, hυ]
    ring
  by_cases hτ : ∀ x, τ x = x
  · apply hfield
    let D : F →+ F := AddMonoidHom.mk' (fun y => y - c * υ y) (fun a b => by
      simp only [map_add]; ring)
    have hDinj : Function.Injective D := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have : G 1 y = 0 := by
        simp only [hG, map_one, one_mul, mul_one]
        exact hy
      rcases h0 1 y this with h1 | h1
      · exact absurd h1 one_ne_zero
      · exact h1
    refine h.trans ⟨AddEquiv.refl F, addEquivOfInjective D hDinj, AddEquiv.refl F,
      fun x y => ?_⟩
    simp only [addEquivOfInjective, AddEquiv.ofBijective_apply, AddEquiv.refl_apply, D,
      AddMonoidHom.mk'_apply, hG, hτ]
    ring
  by_cases hτυ : ∀ x, τ x = υ x
  · apply hfield
    let D : F →+ F := AddMonoidHom.mk' (fun z => z - c * τ z) (fun a b => by
      simp only [map_add]; ring)
    have hDinj : Function.Injective D := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have : G x 1 = 0 := by
        simp only [hG, map_one, mul_one]
        exact hx
      rcases h0 x 1 this with h1 | h1
      · exact h1
      · exact absurd h1 one_ne_zero
    refine h.trans (Isotopic.symm ⟨AddEquiv.refl F, AddEquiv.refl F,
      addEquivOfInjective D hDinj, fun x y => ?_⟩)
    simp only [addEquivOfInjective, AddEquiv.ofBijective_apply, AddEquiv.refl_apply, D,
      AddMonoidHom.mk'_apply, hG, ← hτυ, map_mul]
    ring
  push_neg at hυ hτ hτυ
  -- the Frobenius setting over the prime field
  letI := ZMod.algebra F p
  haveI : NeZero (Module.finrank (ZMod p) F) := ⟨Module.finrank_pos.ne'⟩
  set N := Module.finrank (ZMod p) F
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F
  have hφb : Function.Bijective (fun i : ZMod N => sig φ i) := bijective_sig_frobenius (F := F) p
  obtain ⟨α, hα⟩ : ∃ α : ZMod N, ∀ x, τ x = sig φ α x := exists_sig_frobenius_eq p τ
  obtain ⟨β, hβ⟩ : ∃ β : ZMod N, ∀ x, υ x = sig φ β x := exists_sig_frobenius_eq p υ
  have hφN : φ ^ N = 1 := pow_eq_one_of_bij hφb
  have hlin : ∀ (T : F →+ F) (k : ZMod p) (z : F),
      T (algebraMap (ZMod p) F k * z) = algebraMap (ZMod p) F k * T z := by
    intro T k z
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact ZMod.map_smul T k z
  have hα0 : α ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hτ
    exact hx (by rw [hα]; simp)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hυ
    exact hx (by rw [hβ]; simp)
  have hαβ : α ≠ β := by
    rintro rfl
    obtain ⟨x, hx⟩ := hτυ
    exact hx (by rw [hα, hβ])
  have hGg : G = gtfMul φ c α β := by
    funext x y
    simp only [hG, gtfMul, hα, hβ]
  have hGg' : (fun x y => G y x) = gtfMul φ c β α := by
    funext x y
    simp only [hG, gtfMul, hα, hβ]
    ring
  -- the idealisers of the family have `|K|` elements
  obtain ⟨hId1, hId2, -⟩ := thm_direct_nuclei hq hr5 hr6 hσgen hw
  have hK : Nat.card (scalarMaps K F) = Fintype.card K := by
    rw [card_scalarMaps, Nat.card_eq_fintype_card]
  have hcard1 : Nat.card (leftIdealiser (spreadSet (famMul r σ w)
      (fun y a b => famMul_add_left a b y))) = Fintype.card K := by
    change Nat.card (leftIdealiser (famC r σ w)) = _
    rw [hId2, hK]
  have hcard2 : Nat.card (leftIdealiser (spreadSet (fun a b => famMul r σ w b a)
      (fun x a b => famMul_add_right x a b))) = Fintype.card K := by
    change Nat.card (leftIdealiser (famCd r σ w)) = _
    rw [hId1, hK]
  have hiso1 : Isotopic (famMul r σ w) (gtfMul φ c α β) := hGg ▸ h
  have hiso2 : Isotopic (fun a b => famMul r σ w b a) (gtfMul φ c β α) := by
    obtain ⟨A, B, C, hABC⟩ := h
    rw [← hGg']
    exact ⟨B, A, C, fun x y => hABC y x⟩
  have hfixυ := fixed_eq_range_of_isotopic_gtf (K := K) hφb rfl hφN hlin hc hα0 hβ0 hαβ
    (fun y a b => famMul_add_left a b y) hP.eq_zero_or_eq_zero hcard1 hiso1
  have hfixτ := fixed_eq_range_of_isotopic_gtf (K := K) hφb rfl hφN hlin hc hβ0 hα0
    (Ne.symm hαβ) (fun x a b => famMul_add_right x a b)
    (fun x y hxy => (hP.eq_zero_or_eq_zero y x hxy).symm) hcard2 hiso2
  -- hence `τ` and `υ` fix `K`
  have hτK : ∀ k : K, τ (algebraMap K F k) = algebraMap K F k := by
    intro k
    have : algebraMap K F k ∈ {a : F | sig φ α a = a} := by rw [hfixτ]; exact ⟨k, rfl⟩
    rw [hα]; exact this
  have hυK : ∀ k : K, υ (algebraMap K F k) = algebraMap K F k := by
    intro k
    have : algebraMap K F k ∈ {a : F | sig φ β a = a} := by rw [hfixυ]; exact ⟨k, rfl⟩
    rw [hβ]; exact this
  obtain ⟨α', hα'⟩ := hσgen.2 (AlgEquiv.ofRingEquiv (f := τ) hτK)
  obtain ⟨β', hβ'⟩ := hσgen.2 (AlgEquiv.ofRingEquiv (f := υ) hυK)
  have hτσ : ∀ x, τ x = sig σ α' x := fun x => by
    simp only at hα'; rw [hα']; rfl
  have hυσ : ∀ x, υ x = sig σ β' x := fun x => by
    simp only at hβ'; rw [hβ']; rfl
  -- `G` is `K`-bilinear and its left idealiser consists of `K`-scalars
  have hGl : ∀ (a : K) x y, G (algebraMap K F a * x) y = algebraMap K F a * G x y := by
    intro a x y
    simp only [hG, map_mul, hτK]; ring
  have hGr : ∀ (a : K) x y, G x (algebraMap K F a * y) = algebraMap K F a * G x y := by
    intro a x y
    simp only [hG, map_mul, hυK]; ring
  have haddG : ∀ y, ∀ x₁ x₂, G (x₁ + x₂) y = G x₁ y + G x₂ y := by
    intro y x₁ x₂; simp only [hG, map_add]; ring
  have haddG' : ∀ x, ∀ y₁ y₂, G x (y₁ + y₂) = G x y₁ + G x y₂ := by
    intro x y₁ y₂; simp only [hG, map_add]; ring
  have hGid : leftIdealiser (spreadSet G haddG) ⊆ scalarMaps K F := by
    intro T hT
    have hT' : T ∈ leftIdealiser (spreadSet (gtfMul φ c α β)
        (fun y x₁ x₂ => gtfMul_add_left c α β x₁ x₂ y)) := by
      have e : spreadSet G haddG = spreadSet (gtfMul φ c α β)
          (fun y x₁ x₂ => gtfMul_add_left c α β x₁ x₂ y) := by
        simp only [spreadSet, hGg]
      rw [← e]; exact hT
    have h0' : ∀ x y, gtfMul φ c α β x y = 0 → x = 0 ∨ y = 0 := by rw [← hGg]; exact h0
    obtain ⟨a, ha, hfix⟩ := gtf_leftIdealiser_subset hφb rfl hφN hc hα0 hβ0 hαβ h0'
      (hlin T) hT'
    have : a ∈ Set.range (algebraMap K F) := by rw [← hfixυ]; exact hfix
    obtain ⟨k, rfl⟩ := this
    exact ⟨k, ha⟩
  obtain ⟨j, hj⟩ := isotopicLin_twist_of_isotopic (p := p) (K := K) haddG haddG'
    (fun a x y => famMul_smul_left a x y) (fun a x y => famMul_smul_right a x y)
    hGl hGr h0 hGid h
  rw [twistMul_famMul] at hj
  have hGσ : G = fun x y => x * y - c * sig σ α' x * sig σ β' y := by
    funext x y; simp only [hG, hτσ, hυσ]
  rw [hGσ] at hj
  exact not_isotopicLin_gtf hr hr5 hq hσgen (root_pow (p := p) hw j) c α' β' hj

end Main

end Semifields
