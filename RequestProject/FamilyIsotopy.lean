import RequestProject.Semilinear

/-!
# Isotopisms within the family over a general base field (`thm:parameters`, prime dimension)

For a prime `r ≥ 5` and any finite field `K = 𝔽_q` with `q ≡ 1 (mod 3)`, an arbitrary
(additive) isotopism between two members of the family is, after the Galois twist of
`lem:semilinearity`, a `K`-linear isotopism from `𝒫_{w^{p^j}, s}` to `𝒫_{v, t}`; the `K`-linear
classification then forces `t = s` if `w^{p^j} = v`, and `t = -s` otherwise.
-/

namespace Semifields

open scoped BigOperators

variable {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ} [NeZero r]

omit [Fintype K] [Fintype F] [Algebra K F] [CharP F p] [Fact p.Prime] in
/-- The two roots of `X ^ 2 - X + 1`: if `v ≠ w` then `v = 1 - w`. -/
lemma root_eq_one_sub {v w : K} (hv : v ^ 2 - v + 1 = 0) (hw : w ^ 2 - w + 1 = 0) (hvw : v ≠ w) :
    v = 1 - w := by
  have h : (v - w) * (v - (1 - w)) = 0 := by linear_combination hv - hw
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hvw
  · exact sub_eq_zero.mp h

omit [Fintype K] [Fintype F] [Algebra K F] [CharP F p] in
/-- Roots of `X ^ 2 - X + 1` are carried to roots by powers of the Frobenius. -/
lemma root_pow {w : K} (hw : w ^ 2 - w + 1 = 0) (j : ℕ) [CharP K p] :
    (w ^ p ^ j) ^ 2 - w ^ p ^ j + 1 = 0 := by
  have := congrArg (iterateFrobenius K p j) hw
  rw [map_zero, map_add, map_sub, map_pow, map_one, iterateFrobenius_def] at this
  exact this

omit [Fintype F] in
lemma leftIdealiser_famMul_subset [FiniteDimensional K F] [IsGalois K F]
    (hq : Fintype.card K % 3 = 1) (hr5 : 5 ≤ r) (hr6 : Nat.gcd r 6 = 1)
    {σ : F ≃ₐ[K] F} (hσgen : Function.Bijective (fun i : ZMod r => sig σ i)) {w : K}
    (hw : w ^ 2 - w + 1 = 0) :
    leftIdealiser (spreadSet (famMul r σ w) (fun y a b => famMul_add_left a b y))
      ⊆ scalarMaps K F := by
  have := (thm_direct_nuclei hq hr5 hr6 hσgen hw).2.1
  exact this.le

/-- **Isotopisms between members of the family** (`thm:parameters`, prime dimension, general
`q`).  If `𝒫_{w,s}` and `𝒫_{v,t}` (generators `σ₁`, `σ₂`) are isotopic, then for some `j`,
`t = s` when `w^{p^j} = v` and `t = -s` (i.e. `σ₂ = σ₁⁻¹`) otherwise. -/
theorem famMul_isotopic_cases [CharP K p] (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq : Fintype.card K % 3 = 1) {σ₁ σ₂ : F ≃ₐ[K] F}
    (h₁ : Function.Bijective (fun i : ZMod r => sig σ₁ i))
    (h₂ : Function.Bijective (fun i : ZMod r => sig σ₂ i)) {w v : K}
    (hw : w ^ 2 - w + 1 = 0) (hv : v ^ 2 - v + 1 = 0)
    (h : Isotopic (famMul r σ₁ w) (famMul r σ₂ v)) :
    ∃ j : ℕ, (w ^ p ^ j = v → σ₂ = σ₁) ∧ (w ^ p ^ j ≠ v → σ₂ = sig σ₁ (-1 : ZMod r)) := by
  haveI : FiniteDimensional K F := Module.Finite.of_finite
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod_three hq
  have hr6 : Nat.gcd r 6 = 1 := by
    have : Nat.Coprime r 6 := by
      rw [Nat.Prime.coprime_iff_not_dvd hr]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases r <;> first | omega | norm_num at hr
    exact this
  have hmod := mod_six_of_gcd_six hr6
  have hσ₁ : σ₁ ^ r = 1 := pow_eq_one_of_bij h₁
  have hσ₂ : σ₂ ^ r = 1 := pow_eq_one_of_bij h₂
  have hQ := isPresemifield_famMul hσ₂ hv h3 hmod hr5
  obtain ⟨j, hj⟩ := isotopicLin_twist_of_isotopic (p := p) (K := K)
    (fun y a b => famMul_add_left a b y) (fun x a b => famMul_add_right x a b)
    (fun a x y => famMul_smul_left a x y) (fun a x y => famMul_smul_right a x y)
    (fun a x y => famMul_smul_left a x y) (fun a x y => famMul_smul_right a x y)
    hQ.eq_zero_or_eq_zero (leftIdealiser_famMul_subset hq hr5 hr6 h₂ hv) h
  rw [twistMul_famMul] at hj
  refine ⟨j, fun hwv => ?_, fun hwv => ?_⟩
  · rw [hwv] at hj
    exact (eq_of_isotopicLin_famMul hr hr5 h₁ h₂ hv h3 hj).symm
  · have hroot := root_pow (p := p) hw j
    have e := root_eq_one_sub hroot hv hwv
    rw [e] at hj
    have hneg : IsUnit (-1 : ZMod r) := isUnit_one.neg
    have h₁' := bijective_sig_sig_unit h₁ (-1 : ZMod r) hneg
    exact (eq_of_isotopicLin_famMul hr hr5 h₁' h₂ hv h3
      ((isotopicLin_famMul_neg_one hσ₁ hv).symm.trans hj)).symm

end Semifields
