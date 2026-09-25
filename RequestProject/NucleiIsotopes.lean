import RequestProject.MenichettiFamily

/-!
# Nuclei and centre of every semifield isotopic to the family (`cor:nuclei`)

For admissible parameters, every semifield `(F, +, ∘)` isotopic to `𝒫_{w,s}` has left, middle
and right nuclei and centre of order `|K| = q` (`card_nuclei_of_isotopic`).

The nuclei are counted through the idealisers of the spread sets, which are conjugate under
isotopy (`thm:direct-nuclei`).  For the centre, conjugating the `K`-scalar maps by an isotopism
`(A, B, C)` gives, for each `a ∈ K`, a single map `T_a = A m_a A⁻¹ = B m_a B⁻¹ = C m_a C⁻¹`,
which is left and right multiplication by the central element `T_a(e)`; this yields `|K|`
distinct central elements.
-/

namespace Semifields

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Algebra K F]
  [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

omit [Fintype K] [FiniteDimensional K F] [IsGalois K F] in
/-- The `|K|` central elements of a semifield isotopic to a `K`-bilinear multiplication. -/
theorem card_le_centre_of_isotopic [Finite F] {mulP S : F → F → F}
    (hPl : ∀ (a : K) x y, mulP (algebraMap K F a * x) y = algebraMap K F a * mulP x y)
    (hPr : ∀ (a : K) x y, mulP x (algebraMap K F a * y) = algebraMap K F a * mulP x y)
    (hS : IsSemifield S) (h : Isotopic mulP S) :
    Nat.card K ≤ Nat.card (semifieldCentre S) := by
  obtain ⟨A, B, C, hABC⟩ := h
  obtain ⟨e, he⟩ := hS.exists_one
  let α : K → F → F := fun a u => A (algebraMap K F a * A.symm u)
  let β : K → F → F := fun a v => B (algebraMap K F a * B.symm v)
  let γ : K → F → F := fun a t => C (algebraMap K F a * C.symm t)
  have hα : ∀ a u v, S (α a u) v = γ a (S u v) := by
    intro a u v
    have e1 := hABC (algebraMap K F a * A.symm u) (B.symm v)
    have e2 := hABC (A.symm u) (B.symm v)
    simp only [AddEquiv.apply_symm_apply] at e1 e2
    simp only [α, γ]
    rw [e1, e2, AddEquiv.symm_apply_apply, hPl]
  have hβ : ∀ a u v, S u (β a v) = γ a (S u v) := by
    intro a u v
    have e1 := hABC (A.symm u) (algebraMap K F a * B.symm v)
    have e2 := hABC (A.symm u) (B.symm v)
    simp only [AddEquiv.apply_symm_apply] at e1 e2
    simp only [β, γ]
    rw [e1, e2, AddEquiv.symm_apply_apply, hPr]
  -- all three conjugates agree, and are multiplication by `z a = γ a e` on both sides
  have hβγ : ∀ a v, β a v = γ a v := by
    intro a v
    have := hβ a e v
    rwa [(he _).1, (he _).1] at this
  have hαγ : ∀ a u, α a u = γ a u := by
    intro a u
    have := hα a u e
    rwa [(he _).2, (he _).2] at this
  have hL : ∀ a v, γ a v = S (γ a e) v := by
    intro a v
    rw [← hαγ a e, hα, (he v).1]
  have hR : ∀ a u, γ a u = S u (γ a e) := by
    intro a u
    rw [← hβγ a e, hβ, (he u).2]
  have hcentre : ∀ a, γ a e ∈ semifieldCentre S := by
    intro a
    refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x => ?_⟩
    · rw [← hL a (S x y), ← hL a x, ← hαγ a x, hα]
    · rw [← hL a y, ← hR a x, ← hβγ a y, hβ, ← hαγ a x, hα]
    · rw [← hR a y, ← hR a (S x y), ← hβγ a y, hβ]
    · rw [← hL a x, ← hR a x]
  have he0 : e ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hS.exists_ne_zero
    apply hx
    have h1 := (he x).1
    rw [h0] at h1
    have : S 0 x = 0 := by
      have := hS.add_left 0 0 x
      simpa using this
    rw [← h1, this]
  have hCe : C.symm e ≠ 0 := fun h0 => he0 (by simpa using congrArg C h0)
  exact Nat.card_le_card_of_injective (fun a : K => (⟨γ a e, hcentre a⟩ : semifieldCentre S))
    (fun a b hab => by
      have h1 := congrArg (fun z : semifieldCentre S => C.symm (z : F)) hab
      simp only [γ, AddEquiv.symm_apply_apply] at h1
      exact (algebraMap K F).injective (mul_right_cancel₀ hCe h1))

/-- **`cor:nuclei`.**  For admissible parameters, every semifield multiplication on `F`
isotopic to `𝒫_{w,s}` has left, middle and right nuclei and centre with exactly `|K|`
elements. -/
theorem card_nuclei_of_isotopic (hq : Fintype.card K % 3 = 1) (hn5 : 5 ≤ n)
    (hn6 : Nat.gcd n 6 = 1) (hσgen : Function.Bijective (fun i : ZMod n => sig σ i))
    (hw : w ^ 2 - w + 1 = 0) {S : F → F → F} (hS : IsSemifield S)
    (h : Isotopic (famMul n σ w) S) :
    Nat.card (leftNucleus S) = Fintype.card K ∧
      Nat.card (middleNucleus S) = Fintype.card K ∧
      Nat.card (rightNucleus S) = Fintype.card K ∧
      Nat.card (semifieldCentre S) = Fintype.card K := by
  haveI : Finite F := Module.finite_of_finite K
  obtain ⟨hId1, hId2, hId3⟩ := thm_direct_nuclei hq hn5 hn6 hσgen hw
  have hK : Nat.card (scalarMaps K F) = Fintype.card K := by
    rw [card_scalarMaps, Nat.card_eq_fintype_card]
  have hcentre := card_le_centre_of_isotopic (fun a x y => famMul_smul_left a x y)
    (fun a x y => famMul_smul_right a x y) hS h
  obtain ⟨A, B, C, hABC⟩ := h
  obtain ⟨e, he⟩ := hS.exists_one
  have hR : Nat.card (rightNucleus S) = Fintype.card K := by
    rw [card_rightNucleus (fun y a b => hS.add_left a b y) he,
      card_leftIdealiser_eq (haddP := fun y a b => famMul_add_left a b y) hABC]
    change Nat.card (leftIdealiser (famC n σ w)) = _
    rw [hId2, hK]
  refine ⟨?_, ?_, hR, ?_⟩
  · rw [card_leftNucleus he (fun x a b => hS.add_right x a b)]
    change Nat.card (leftIdealiser (spreadSet (fun a b => S b a)
      (fun x a b => hS.add_right x a b))) = _
    rw [card_leftIdealiser_eq (haddP := fun x a b => famMul_add_right x a b)
      (mulP := fun a b => famMul n σ w b a) (A := B) (B := A) (C := C)
      (fun x y => hABC y x)]
    change Nat.card (leftIdealiser (famCd n σ w)) = _
    rw [hId1, hK]
  · rw [card_middleNucleus (fun y a b => hS.add_left a b y) he,
      card_rightIdealiser_eq (haddP := fun y a b => famMul_add_left a b y) hABC]
    change Nat.card (rightIdealiser (famC n σ w)) = _
    rw [hId3, hK]
  · apply le_antisymm
    · rw [← hR]
      exact Nat.card_mono (Set.toFinite _) (fun a ha => ha.2.2.1)
    · rw [← Nat.card_eq_fintype_card]
      exact hcentre

end Semifields
