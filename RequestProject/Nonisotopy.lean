import RequestProject.Idealisers
import RequestProject.Admissible

/-!
# Exclusion of field isotopes (`thm:nonisotopy`, field case)

The left idealiser of the spread set is an isotopy invariant up to conjugation.  For the
field multiplication of `F` this idealiser contains all the multiplications `m_a`, `a ∈ F`,
while for the family `𝒫_{w,s}` it consists of the `K`-scalar multiplications only
(`thm:direct-nuclei`).  Since `|F| = |K| ^ n > |K|`, the family is not isotopic to a field.
-/

namespace Semifields

open scoped BigOperators

section FieldCase

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [FiniteDimensional K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

omit [Fintype K] [Fintype F] [FiniteDimensional K F] in
/-- If the family is isotopic to the field multiplication of `F`, then conjugation by the
third map of the isotopism carries each `m_a`, `a ∈ F`, into the left idealiser of the
spread set of the family. -/
lemma mem_leftIdealiser_famC_of_isotopic_field
    {A B C : F ≃+ F} (hABC : ∀ x y : F, (A x) * (B y) = C (famMul n σ w x y)) (a : F) :
    ((C.symm.toAddMonoidHom.comp ((AddMonoidHom.mulLeft a).comp C.toAddMonoidHom)) :
        F →+ F) ∈ leftIdealiser (famC n σ w) := by
  rw [mem_leftIdealiser_famC]
  intro y
  refine ⟨B.symm (a * B y), fun x => ?_⟩
  have h1 : C (famMul n σ w x y) = A x * B y := (hABC x y).symm
  have h2 : C (famMul n σ w x (B.symm (a * B y))) = A x * (a * B y) := by
    rw [← hABC x (B.symm (a * B y))]
    simp
  have h3 : a * C (famMul n σ w x y) = C (famMul n σ w x (B.symm (a * B y))) := by
    rw [h1, h2]; ring
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
    AddEquiv.coe_toAddMonoidHom]
  rw [h3]
  exact C.symm_apply_apply _

/-- **`thm:nonisotopy`, field case.**  No member of the family is isotopic to the field
multiplication of `F`.  (Any presemifield isotopic to `𝒫_{w,s}` has `|F|` elements, so the
only finite field that could occur is a field of order `|F|`.) -/
theorem not_isotopic_field (hq : Fintype.card K % 3 = 1) (hn5 : 5 ≤ n) (hn6 : Nat.gcd n 6 = 1)
    (hσgen : Function.Bijective (fun i : ZMod n => sig σ i)) (hw : w ^ 2 - w + 1 = 0)
    [IsGalois K F] :
    ¬ Isotopic (famMul n σ w) (fun x y : F => x * y) := by
  rintro ⟨A, B, C, hABC⟩
  have hmod := mod_six_of_gcd_six hn6
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod_three hq
  have hcardG : Fintype.card (F ≃ₐ[K] F) = n := by
    rw [← Fintype.card_of_bijective hσgen, ZMod.card]
  have hσ : σ ^ n = 1 := by rw [← hcardG]; exact pow_card_eq_one
  have hfin : Module.finrank K F = n := by
    rw [← IsGalois.card_aut_eq_finrank K F, Nat.card_eq_fintype_card, hcardG]
  have hcn6 : Nat.Coprime n 6 := hn6
  have hcop3 : Nat.Coprime 3 n := (Nat.Coprime.coprime_dvd_right (by norm_num) hcn6).symm
  have hcop2 : Nat.Coprime 2 n := (Nat.Coprime.coprime_dvd_right (by norm_num) hcn6).symm
  have hcop : Nat.Coprime 4 n := by
    have h22 : Nat.Coprime (2 * 2) n := Nat.Coprime.mul_left hcop2 hcop2
    simpa using h22
  have hP := isPresemifield_famMul hσ hw h3 hmod hn5
  have hIl := leftIdealiser_famC_eq hσgen hfin hσ hn5 hcop hw hP hcop3
  -- every `a : F` determines an element of `K`
  have hkey : ∀ a : F, ∃ k : K, ∀ z : F, C.symm (a * C z) = algebraMap K F k * z := by
    intro a
    have hmem := mem_leftIdealiser_famC_of_isotopic_field hABC a
    rw [hIl] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, fun z => ?_⟩
    have hz := hk z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddEquiv.coe_toAddMonoidHom] at hz
    exact hz
  choose f hf using hkey
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a 1
    have h2 := hf b 1
    rw [hab] at h1
    have h3 : a * C 1 = b * C 1 := by
      have := h1.trans h2.symm
      exact C.symm.injective this
    have hC1 : C (1 : F) ≠ 0 := by
      intro hcon
      have h0 := congrArg C.symm hcon
      simp only [AddEquiv.symm_apply_apply, map_zero] at h0
      exact one_ne_zero h0
    exact mul_right_cancel₀ hC1 h3
  -- but `F` is much bigger than `K`
  have hcard : Fintype.card F ≤ Fintype.card K := Fintype.card_le_of_injective f hinj
  have hpow : Fintype.card F = Fintype.card K ^ n := by
    rw [← hfin]
    exact Module.card_eq_pow_finrank
  have h1K : 1 < Fintype.card K := Fintype.one_lt_card
  have : Fintype.card K ^ 1 < Fintype.card K ^ n :=
    Nat.pow_lt_pow_right h1K (by omega)
  rw [pow_one] at this
  omega

end FieldCase

end Semifields
