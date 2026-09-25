import RequestProject.MainResults
import RequestProject.GTF
import RequestProject.SemifieldBasics

/-!
# The semifields attached to the family (`lem:kaplansky`, `cor:nuclei`)

For admissible parameters, Kaplansky's trick with `a = 1` turns the presemifield
`𝒫_{w,s} = (F, +, *)` into an isotopic semifield `famSemi n σ w`,
`x ∘ y = R_1⁻¹(x) * L_1⁻¹(y)`, with identity `1 * 1`.

* `isSemifield_famSemi`, `isotopic_famSemi` : it is a semifield isotopic to `𝒫_{w,s}`;
* `card_nuclei_famSemi` : its left, middle and right nuclei and its centre all have exactly
  `|K|` elements (`cor:nuclei`), obtained from `thm:direct-nuclei` through the correspondence
  between nuclei and idealisers of spread sets.
-/

namespace Semifields

section KaplanskyFamily

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

open Classical in
/-- The right multiplication `R_1 : x ↦ x * 1` of the family, as an additive bijection
(when it is one). -/
noncomputable def famRa (n : ℕ) [NeZero n] (σ : F ≃ₐ[K] F) (w : K) : F ≃+ F :=
  if h : Function.Bijective (fun x => famMul n σ w x 1) then
    AddEquiv.ofBijective (AddMonoidHom.mk' (fun x => famMul n σ w x 1)
      (fun a b => famMul_add_left a b 1)) h
  else AddEquiv.refl F

open Classical in
/-- The left multiplication `L_1 : y ↦ 1 * y` of the family, as an additive bijection
(when it is one). -/
noncomputable def famLa (n : ℕ) [NeZero n] (σ : F ≃ₐ[K] F) (w : K) : F ≃+ F :=
  if h : Function.Bijective (fun y => famMul n σ w 1 y) then
    AddEquiv.ofBijective (AddMonoidHom.mk' (fun y => famMul n σ w 1 y)
      (fun a b => famMul_add_right 1 a b)) h
  else AddEquiv.refl F

/-- The semifield obtained from `𝒫_{w,s}` by Kaplansky's trick (`lem:kaplansky`) with
`a = 1`: `x ∘ y = R_1⁻¹(x) * L_1⁻¹(y)`. -/
noncomputable def famSemi (n : ℕ) [NeZero n] (σ : F ≃ₐ[K] F) (w : K) : F → F → F :=
  kapMul (famMul n σ w) (famRa n σ w) (famLa n σ w)

/-- The semifield `famSemi n σ w` is isotopic to the presemifield `𝒫_{w,s}`. -/
theorem isotopic_famSemi : Isotopic (famMul n σ w) (famSemi n σ w) := isotopic_kapMul

lemma famMul_sub_left' (x₁ x₂ y : F) :
    famMul n σ w (x₁ - x₂) y = famMul n σ w x₁ y - famMul n σ w x₂ y :=
  ((famMulₗ n σ w).flip y).map_sub x₁ x₂

lemma famMul_sub_right' (x y₁ y₂ : F) :
    famMul n σ w x (y₁ - y₂) = famMul n σ w x y₁ - famMul n σ w x y₂ :=
  (famMulₗ n σ w x).map_sub y₁ y₂

lemma famMul_smul_left' (c : K) (x y : F) :
    famMul n σ w (c • x) y = c • famMul n σ w x y :=
  ((famMulₗ n σ w).flip y).map_smul c x

lemma famMul_smul_right' (c : K) (x y : F) :
    famMul n σ w x (c • y) = c • famMul n σ w x y :=
  (famMulₗ n σ w x).map_smul c y

variable [Finite F] (hP : IsPresemifield K (famMulₗ n σ w))
include hP

lemma bijective_famMul_one_right : Function.Bijective (fun x => famMul n σ w x 1) := by
  refine Finite.injective_iff_bijective.mp (fun a b h => ?_)
  have h0 : famMul n σ w (a - b) 1 = 0 := by
    rw [famMul_sub_left']; exact sub_eq_zero.mpr h
  rcases hP.eq_zero_or_eq_zero (a - b) 1 h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 one_ne_zero

lemma bijective_famMul_one_left : Function.Bijective (fun y => famMul n σ w 1 y) := by
  refine Finite.injective_iff_bijective.mp (fun a b h => ?_)
  have h0 : famMul n σ w 1 (a - b) = 0 := by
    rw [famMul_sub_right']; exact sub_eq_zero.mpr h
  rcases hP.eq_zero_or_eq_zero 1 (a - b) h0 with h1 | h1
  · exact absurd h1 one_ne_zero
  · exact sub_eq_zero.mp h1

lemma famRa_apply (x : F) : famRa n σ w x = famMul n σ w x 1 := by
  rw [famRa, dif_pos (bijective_famMul_one_right hP)]; rfl

lemma famLa_apply (y : F) : famLa n σ w y = famMul n σ w 1 y := by
  rw [famLa, dif_pos (bijective_famMul_one_left hP)]; rfl

/-- `famSemi n σ w` is a semifield (`lem:kaplansky`). -/
theorem isSemifield_famSemi : IsSemifield (famSemi n σ w) :=
  isSemifield_kapMul (fun a b y => famMul_add_left a b y) (fun x a b => famMul_add_right x a b)
    (fun x y h => hP.eq_zero_or_eq_zero x y h) one_ne_zero (famRa_apply hP) (famLa_apply hP)

lemma famRa_symm_smul (c : K) (x : F) :
    (famRa n σ w).symm (c • x) = c • (famRa n σ w).symm x := by
  rw [AddEquiv.symm_apply_eq, famRa_apply hP, famMul_smul_left', ← famRa_apply hP,
    AddEquiv.apply_symm_apply]

lemma famLa_symm_smul (c : K) (y : F) :
    (famLa n σ w).symm (c • y) = c • (famLa n σ w).symm y := by
  rw [AddEquiv.symm_apply_eq, famLa_apply hP, famMul_smul_right', ← famLa_apply hP,
    AddEquiv.apply_symm_apply]

lemma famSemi_smul_left (c : K) (x y : F) :
    famSemi n σ w (c • x) y = c • famSemi n σ w x y := by
  simp only [famSemi, kapMul, famRa_symm_smul hP, famMul_smul_left']

lemma famSemi_smul_right (c : K) (x y : F) :
    famSemi n σ w x (c • y) = c • famSemi n σ w x y := by
  simp only [famSemi, kapMul, famLa_symm_smul hP, famMul_smul_right']

/-- `1 * 1` is the identity of `famSemi n σ w`. -/
lemma famSemi_one (x : F) :
    famSemi n σ w (famMul n σ w 1 1) x = x ∧ famSemi n σ w x (famMul n σ w 1 1) = x := by
  constructor
  · simp only [famSemi, kapMul]
    have : (famRa n σ w).symm (famMul n σ w 1 1) = 1 := by
      rw [AddEquiv.symm_apply_eq, famRa_apply hP]
    rw [this, ← famLa_apply hP, AddEquiv.apply_symm_apply]
  · simp only [famSemi, kapMul]
    have : (famLa n σ w).symm (famMul n σ w 1 1) = 1 := by
      rw [AddEquiv.symm_apply_eq, famLa_apply hP]
    rw [this, ← famRa_apply hP, AddEquiv.apply_symm_apply]

omit [Finite F] hP in
lemma famSemi_isotopism (x y : F) :
    famSemi n σ w (famRa n σ w x) (famLa n σ w y) = AddEquiv.refl F (famMul n σ w x y) := by
  simp [famSemi, kapMul]

omit [Finite F] hP in
lemma famSemi_flip_isotopism (x y : F) :
    (fun a b => famSemi n σ w b a) (famLa n σ w x) (famRa n σ w y)
      = AddEquiv.refl F ((fun a b => famMul n σ w b a) x y) := by
  simp [famSemi, kapMul]

/-- The `K`-multiples of the identity lie in the centre of `famSemi n σ w`. -/
lemma smul_one_mem_centre (c : K) :
    c • famMul n σ w 1 1 ∈ semifieldCentre (famSemi n σ w) := by
  have he := famSemi_one hP
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x => ?_⟩ <;>
    simp only [famSemi_smul_left hP, famSemi_smul_right hP, (he _).1, (he _).2]

end KaplanskyFamily

section Nuclei

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Algebra K F]
  [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

omit [Fintype K] [FiniteDimensional K F] [IsGalois K F] in
lemma card_scalarMaps : Nat.card (scalarMaps K F) = Nat.card K := by
  symm
  refine Nat.card_eq_of_bijective
    (fun a : K => (⟨AddMonoidHom.mulLeft (algebraMap K F a), ⟨a, fun x => rfl⟩⟩ :
      scalarMaps K F)) ⟨fun a b h => ?_, fun T => ?_⟩
  · have := congrArg (fun T : scalarMaps K F => (T : F →+ F) 1) h
    simp only [AddMonoidHom.coe_mulLeft, mul_one] at this
    exact (algebraMap K F).injective this
  · obtain ⟨T, a, ha⟩ := T
    exact ⟨a, Subtype.ext (AddMonoidHom.ext fun x => (ha x).symm)⟩

/-- **`cor:nuclei` for the Kaplansky semifields.**  For admissible parameters, the left,
middle and right nuclei and the centre of the semifield `famSemi n σ w` all have exactly `|K|`
elements. -/
theorem card_nuclei_famSemi (hq : Fintype.card K % 3 = 1) (hn5 : 5 ≤ n) (hn6 : Nat.gcd n 6 = 1)
    (hσgen : Function.Bijective (fun i : ZMod n => sig σ i)) (hw : w ^ 2 - w + 1 = 0) :
    Nat.card (leftNucleus (famSemi n σ w)) = Fintype.card K ∧
      Nat.card (middleNucleus (famSemi n σ w)) = Fintype.card K ∧
      Nat.card (rightNucleus (famSemi n σ w)) = Fintype.card K ∧
      Nat.card (semifieldCentre (famSemi n σ w)) = Fintype.card K := by
  haveI : Finite F := Module.finite_of_finite K
  have hmod := mod_six_of_gcd_six hn6
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod_three hq
  have hσ : σ ^ n = 1 := pow_eq_one_of_bij hσgen
  have hP := isPresemifield_famMul hσ hw h3 hmod hn5
  obtain ⟨hId1, hId2, hId3⟩ := thm_direct_nuclei hq hn5 hn6 hσgen hw
  have hS := isSemifield_famSemi hP
  have he := famSemi_one hP
  have hK : Nat.card (scalarMaps K F) = Fintype.card K := by
    rw [card_scalarMaps, Nat.card_eq_fintype_card]
  have hR : Nat.card (rightNucleus (famSemi n σ w)) = Fintype.card K := by
    rw [card_rightNucleus (fun y a b => hS.add_left a b y) he,
      card_leftIdealiser_eq (haddP := fun y a b => famMul_add_left a b y)
        (famSemi_isotopism (n := n) (σ := σ) (w := w))]
    change Nat.card (leftIdealiser (famC n σ w)) = _
    rw [hId2, hK]
  refine ⟨?_, ?_, hR, ?_⟩
  · rw [card_leftNucleus he (fun x a b => hS.add_right x a b)]
    change Nat.card (leftIdealiser (spreadSet (fun a b => famSemi n σ w b a)
      (fun x a b => hS.add_right x a b))) = _
    rw [card_leftIdealiser_eq (haddP := fun x a b => famMul_add_right x a b)
        (famSemi_flip_isotopism (n := n) (σ := σ) (w := w))]
    change Nat.card (leftIdealiser (famCd n σ w)) = _
    rw [hId1, hK]
  · rw [card_middleNucleus (fun y a b => hS.add_left a b y) he,
      card_rightIdealiser_eq (haddP := fun y a b => famMul_add_left a b y)
        (famSemi_isotopism (n := n) (σ := σ) (w := w))]
    change Nat.card (rightIdealiser (famC n σ w)) = _
    rw [hId3, hK]
  · apply le_antisymm
    · rw [← hR]
      exact Nat.card_mono (Set.toFinite _) (fun a ha => ha.2.2.1)
    · have he0 : famMul n σ w 1 1 ≠ 0 := fun h0 => by
        rcases hP.eq_zero_or_eq_zero 1 1 h0 with h | h <;> exact one_ne_zero h
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_le_card_of_injective
        (fun c : K => (⟨c • famMul n σ w 1 1, smul_one_mem_centre hP c⟩ :
          semifieldCentre (famSemi n σ w)))
        (fun c d h => smul_left_injective K he0 (congrArg Subtype.val h))

end Nuclei

end Semifields
