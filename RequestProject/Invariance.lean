import RequestProject.Profile

/-!
# Invariance of the determinant profile (`thm:invariance`)

For a `K`-bilinear presemifield multiplication on `K ^ n` the paper attaches, to each of the
three determinant types `μ ∈ {L, R, tr}`, the *relative determinant profile*
`eq:relative-profile`

`I_{μ,K}(𝒫) = ([E_{μ,K}(𝒫) : K], d_{μ,K}, ρ_{μ,K}(𝒫))`,

where `E_{μ,K}` is the component splitting field of the determinant form `D_μ`
(`def:splittingfield`), `d_{μ,K}` the common degree of its absolutely irreducible factors and
`ρ_{μ,K}` the determinant-vertex rank (`def:vertex`).

This file formalises the three ingredients over a fixed extension field `Ω` of `K` (think of
`Ω` as an algebraic closure of `K`):

* `componentField K' D` : the smallest subfield of `Ω` containing `K'` over which every
  irreducible factor of `D` is defined up to a nonzero scalar;
* `absFactorDegrees D` : the set of degrees of the irreducible factors of `D` (a single value
  `d` by `prop:splittingfield`);
* `IsDetVertex D v`, `vertexRanks D M` : the determinant vertices of `D` — the points at
  which exactly one class of irreducible factors of `D` is nonzero — and the set of ranks of
  the pencil `M` at those points (empty exactly when the symbol `⊥` of `eq:vertexinvariant`
  applies).

The main result, `profile_transport`, shows that all three are unchanged when the
determinant form is transformed by an invertible linear substitution of the variables and a
nonzero scalar factor and the pencil ranks are transported accordingly — which by
`eq:pencilisotopy` (the results of `RequestProject.Profile`) is exactly what a `K`-linear
isotopism does.  Theorem `thm:invariance` for `K`-linear isotopy is assembled from it in
`MainResults.lean`.
-/

namespace Semifields

open scoped BigOperators
open MvPolynomial

section Subst

variable {n : ℕ} {Ω : Type*} [Field Ω]

/-- The substitution `X i ↦ ∑ j, S i j * X j` of the variables by an `Ω`-matrix. -/
noncomputable def substAlg (S : Matrix (Fin n) (Fin n) Ω) :
    MvPolynomial (Fin n) Ω →ₐ[Ω] MvPolynomial (Fin n) Ω :=
  bind₁ fun i => ∑ j, C (S i j) * X j

@[simp] lemma substAlg_X (S : Matrix (Fin n) (Fin n) Ω) (i : Fin n) :
    substAlg S (X i) = ∑ j, C (S i j) * X j := by simp [substAlg]

lemma substAlg_comp (S T : Matrix (Fin n) (Fin n) Ω) (p : MvPolynomial (Fin n) Ω) :
    substAlg S (substAlg T p) = substAlg (T * S) p := by
  have h : (substAlg S).comp (substAlg T) = substAlg (T * S) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, substAlg_X, map_sum, map_mul, algHom_C, Matrix.mul_apply,
      algebraMap_eq, map_sum]
    calc ∑ j, C (T i j) * ∑ k, C (S j k) * X k
        = ∑ j, ∑ k, C (T i j) * (C (S j k) * X k) :=
          Finset.sum_congr rfl fun j _ => Finset.mul_sum ..
      _ = ∑ k, ∑ j, C (T i j) * (C (S j k) * X k) := Finset.sum_comm
      _ = ∑ k, (∑ j, C (T i j) * C (S j k)) * X k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  exact congrArg (fun f => f p) h

lemma substAlg_one (p : MvPolynomial (Fin n) Ω) : substAlg 1 p = p := by
  have h : substAlg (1 : Matrix (Fin n) (Fin n) Ω) = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Matrix.one_apply, Finset.sum_ite_eq]
  exact congrArg (fun f => f p) h

lemma aeval_substAlg (S : Matrix (Fin n) (Fin n) Ω) (v : Fin n → Ω)
    (p : MvPolynomial (Fin n) Ω) :
    aeval v (substAlg S p) = aeval (S.mulVec v) p := by
  have h : (aeval v : MvPolynomial (Fin n) Ω →ₐ[Ω] Ω).comp (substAlg S) = aeval (S.mulVec v) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Matrix.mulVec, dotProduct]
  exact congrArg (fun f => f p) h

lemma eval_substAlg (S : Matrix (Fin n) (Fin n) Ω) (v : Fin n → Ω)
    (p : MvPolynomial (Fin n) Ω) :
    eval v (substAlg S p) = eval (S.mulVec v) p := aeval_substAlg S v p

/-- An invertible substitution is an algebra automorphism of the polynomial ring. -/
noncomputable def substEquiv {S T : Matrix (Fin n) (Fin n) Ω} (h1 : S * T = 1) (h2 : T * S = 1) :
    MvPolynomial (Fin n) Ω ≃ₐ[Ω] MvPolynomial (Fin n) Ω :=
  AlgEquiv.ofAlgHom (substAlg S) (substAlg T)
    (by apply MvPolynomial.algHom_ext; intro i
        simp only [AlgHom.comp_apply, AlgHom.id_apply]
        rw [substAlg_comp, h2, substAlg_one])
    (by apply MvPolynomial.algHom_ext; intro i
        simp only [AlgHom.comp_apply, AlgHom.id_apply]
        rw [substAlg_comp, h1, substAlg_one])

@[simp] lemma substEquiv_apply {S T : Matrix (Fin n) (Fin n) Ω} (h1 : S * T = 1) (h2 : T * S = 1)
    (p : MvPolynomial (Fin n) Ω) : substEquiv h1 h2 p = substAlg S p := rfl

/-- The total degree does not increase under a linear substitution of the variables. -/
lemma substAlg_totalDegree_le (S : Matrix (Fin n) (Fin n) Ω) (p : MvPolynomial (Fin n) Ω) :
    (substAlg S p).totalDegree ≤ p.totalDegree := by
  have hlin : ∀ i : Fin n, (∑ j, C (S i j) * X j : MvPolynomial (Fin n) Ω).totalDegree ≤ 1 := by
    intro i
    refine le_trans (totalDegree_finset_sum _ _) ?_
    refine Finset.sup_le fun j _ => ?_
    refine le_trans (totalDegree_mul _ _) ?_
    simp [totalDegree_C, totalDegree_X]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine le_trans (totalDegree_finset_sum _ _) ?_
  refine Finset.sup_le fun m hm => ?_
  rw [substAlg, bind₁_monomial]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  have hterm : ∀ i ∈ m.support,
      ((∑ j, C (S i j) * X j : MvPolynomial (Fin n) Ω) ^ m i).totalDegree ≤ m i := by
    intro i _
    refine le_trans (totalDegree_pow _ _) ?_
    calc m i * (∑ j, C (S i j) * X j : MvPolynomial (Fin n) Ω).totalDegree
        ≤ m i * 1 := Nat.mul_le_mul_left _ (hlin i)
      _ = m i := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have : ∑ i ∈ m.support, m i = m.sum fun _ e => e := rfl
  rw [this]
  exact le_totalDegree hm

lemma substAlg_totalDegree {S T : Matrix (Fin n) (Fin n) Ω} (h1 : S * T = 1)
    (p : MvPolynomial (Fin n) Ω) : (substAlg S p).totalDegree = p.totalDegree := by
  refine le_antisymm (substAlg_totalDegree_le S p) ?_
  have hp : substAlg T (substAlg S p) = p := by rw [substAlg_comp, h1, substAlg_one]
  calc p.totalDegree = (substAlg T (substAlg S p)).totalDegree := by rw [hp]
    _ ≤ (substAlg S p).totalDegree := substAlg_totalDegree_le _ _

end Subst

section Coeffs

variable {n : ℕ} {Ω : Type*} [Field Ω]

/-- The subring of polynomials all of whose coefficients lie in a given subfield. -/
def coeffsIn (E : Subfield Ω) : Subring (MvPolynomial (Fin n) Ω) where
  carrier := {p | ∀ m, coeff m p ∈ E}
  zero_mem' := by intro m; simp
  one_mem' := by
    intro m
    rw [coeff_one]
    split_ifs <;> simp
  add_mem' := by
    intro p q hp hq m
    rw [coeff_add]
    exact E.add_mem (hp m) (hq m)
  neg_mem' := by
    intro p hp m
    rw [coeff_neg]
    exact E.neg_mem (hp m)
  mul_mem' := by
    intro p q hp hq m
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => E.mul_mem (hp x.1) (hq x.2)

lemma mem_coeffsIn {E : Subfield Ω} {p : MvPolynomial (Fin n) Ω} :
    p ∈ coeffsIn E ↔ ∀ m, coeff m p ∈ E := Iff.rfl

lemma C_mem_coeffsIn {E : Subfield Ω} {a : Ω} (ha : a ∈ E) :
    (C a : MvPolynomial (Fin n) Ω) ∈ coeffsIn E := by
  intro m
  rw [coeff_C]
  split_ifs <;> simp [ha]

lemma X_mem_coeffsIn {E : Subfield Ω} (i : Fin n) :
    (X i : MvPolynomial (Fin n) Ω) ∈ coeffsIn E := by
  intro m
  rw [coeff_X']
  split_ifs <;> simp

/-- A substitution with entries in `E` maps polynomials with coefficients in `E` to
polynomials with coefficients in `E`. -/
lemma substAlg_mem_coeffsIn {E : Subfield Ω} {S : Matrix (Fin n) (Fin n) Ω}
    (hS : ∀ i j, S i j ∈ E) {p : MvPolynomial (Fin n) Ω} (hp : p ∈ coeffsIn E) :
    substAlg S p ∈ coeffsIn E := by
  have hlin : ∀ i : Fin n, (∑ j, C (S i j) * X j : MvPolynomial (Fin n) Ω) ∈ coeffsIn E := by
    intro i
    exact Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ (C_mem_coeffsIn (hS i j)) (X_mem_coeffsIn j)
  have hsum : substAlg S p = ∑ m ∈ p.support, substAlg S (monomial m (coeff m p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine Subring.sum_mem _ fun m _ => ?_
  rw [substAlg, bind₁_monomial]
  exact Subring.mul_mem _ (C_mem_coeffsIn (hp m))
    (Subring.prod_mem _ fun i _ => Subring.pow_mem _ (hlin i) _)

end Coeffs

section ProfileData

variable {n : ℕ} {Ω : Type*} [Field Ω]

/-- A polynomial is defined over `E` up to a scalar if some nonzero multiple of it has all
its coefficients in `E`. -/
def DefinedOverUpToScalar (E : Subfield Ω) (p : MvPolynomial (Fin n) Ω) : Prop :=
  ∃ u : Ω, u ≠ 0 ∧ C u * p ∈ coeffsIn E

/-- Every absolutely irreducible factor of `D` is defined over `E` up to a scalar. -/
def AllFactorsDefinedOver (E : Subfield Ω) (D : MvPolynomial (Fin n) Ω) : Prop :=
  ∀ p : MvPolynomial (Fin n) Ω, Irreducible p → p ∣ D → DefinedOverUpToScalar E p

/-- The component splitting field `E_K(D)` of `def:splittingfield`: the smallest subfield of
`Ω` containing `K'` over which all absolutely irreducible factors of `D` are defined up to a
scalar. -/
def componentField (K' : Subfield Ω) (D : MvPolynomial (Fin n) Ω) : Subfield Ω :=
  sInf {E : Subfield Ω | K' ≤ E ∧ AllFactorsDefinedOver E D}

/-- The set of degrees of the absolutely irreducible factors of `D`; by
`prop:splittingfield` it is a single value `d` for a determinant form of a presemifield. -/
def absFactorDegrees (D : MvPolynomial (Fin n) Ω) : Set ℕ :=
  {d | ∃ p : MvPolynomial (Fin n) Ω, Irreducible p ∧ p ∣ D ∧ p.totalDegree = d}

/-- A *determinant vertex* of `D`: a nonzero point at which exactly one class of associated
irreducible factors of `D` does not vanish.  For `D = λ ℓ_0 ⋯ ℓ_{n-1}` with independent
linear forms these are precisely the vertices `v_i = ⋂_{j ≠ i} {ℓ_j = 0}` of
`def:vertex`. -/
def IsDetVertex (D : MvPolynomial (Fin n) Ω) (v : Fin n → Ω) : Prop :=
  v ≠ 0 ∧ ∃ p : MvPolynomial (Fin n) Ω, Irreducible p ∧ p ∣ D ∧ eval v p ≠ 0 ∧
    ∀ q : MvPolynomial (Fin n) Ω, Irreducible q → q ∣ D → ¬ Associated q p → eval v q = 0

/-- The set of ranks of the pencil `M` at the determinant vertices of `D`.  It is the
extended determinant-vertex rank `eq:vertexinvariant`: a singleton `{ρ}` in the
linear-component case, and empty (the symbol `⊥`) when there are no determinant vertices. -/
def vertexRanks (D : MvPolynomial (Fin n) Ω)
    (M : (Fin n → Ω) → Matrix (Fin n) (Fin n) Ω) : Set ℕ :=
  {r | ∃ v, IsDetVertex D v ∧ (M v).rank = r}

end ProfileData

section Transport

variable {n : ℕ} {Ω : Type*} [Field Ω]
variable {S T : Matrix (Fin n) (Fin n) Ω} {DP DQ : MvPolynomial (Fin n) Ω} {κ : Ω}

/-- Divisors transport along an invertible substitution. -/
lemma dvd_substAlg_iff (h1 : S * T = 1) (p q : MvPolynomial (Fin n) Ω) :
    substAlg S p ∣ substAlg S q ↔ p ∣ q := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨substAlg T r, ?_⟩
    have := congrArg (substAlg T) hr
    rwa [map_mul, substAlg_comp, substAlg_comp, h1, substAlg_one, substAlg_one] at this
  · rintro ⟨r, hr⟩
    exact ⟨substAlg S r, by rw [hr, map_mul]⟩

lemma irreducible_substAlg_iff (h1 : S * T = 1) (h2 : T * S = 1) (p : MvPolynomial (Fin n) Ω) :
    Irreducible (substAlg S p) ↔ Irreducible p :=
  (MulEquiv.irreducible_iff (f := (substEquiv h1 h2).toMulEquiv) (x := p) :
    Irreducible (substAlg S p) ↔ Irreducible p)

lemma associated_substAlg_iff (h1 : S * T = 1) (p q : MvPolynomial (Fin n) Ω) :
    Associated (substAlg S p) (substAlg S q) ↔ Associated p q := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Units.map (substAlg T : MvPolynomial (Fin n) Ω →* MvPolynomial (Fin n) Ω) u, ?_⟩
    have h := congrArg (substAlg T) hu
    rw [map_mul, substAlg_comp, substAlg_comp, h1, substAlg_one, substAlg_one] at h
    simpa using h
  · intro h
    exact h.map (substAlg S : MvPolynomial (Fin n) Ω →* MvPolynomial (Fin n) Ω)

variable (h1 : S * T = 1) (h2 : T * S = 1) (hκ : κ ≠ 0) (hD : substAlg S DQ = C κ * DP)
include h1 h2 hκ hD

omit h1 h2 in
/-- The irreducible factors of `D_Q` correspond to those of `D_P`. -/
lemma dvd_of_dvd_substAlg {p : MvPolynomial (Fin n) Ω} (hp : p ∣ DQ) : substAlg S p ∣ DP := by
  have h : substAlg S p ∣ C κ * DP := by rw [← hD]; exact map_dvd _ hp
  have hDP : DP = C κ⁻¹ * (C κ * DP) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
  rw [hDP]
  exact Dvd.dvd.mul_left h _

omit h2 hκ in
lemma dvd_substAlg_of_dvd {p : MvPolynomial (Fin n) Ω} (hp : p ∣ DP) : substAlg T p ∣ DQ := by
  have hDQ : DQ = substAlg T (C κ * DP) := by
    rw [← hD, substAlg_comp, h1, substAlg_one]
  rw [hDQ, map_mul]
  exact Dvd.dvd.mul_left (map_dvd _ hp) _

omit h2 in
/-- The relation between the two determinant forms, read in the opposite direction. -/
lemma substAlg_symm : substAlg T DP = C κ⁻¹ * DQ := by
  have h : substAlg T (substAlg S DQ) = DQ := by rw [substAlg_comp, h1, substAlg_one]
  rw [hD, map_mul, algHom_C] at h
  simp only [algebraMap_eq] at h
  calc substAlg T DP = C κ⁻¹ * (C κ * substAlg T DP) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
    _ = C κ⁻¹ * DQ := by rw [h]

/-- One direction of the transport of determinant vertices. -/
lemma isDetVertex_of_isDetVertex (v : Fin n → Ω) (hv : IsDetVertex DP v) :
    IsDetVertex DQ (S.mulVec v) := by
  obtain ⟨hv0, p, hpirr, hpdvd, hpev, hother⟩ := hv
  have hSv : S.mulVec v ≠ 0 := by
    intro hcon
    apply hv0
    have : T.mulVec (S.mulVec v) = v := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    rw [hcon, Matrix.mulVec_zero] at this
    exact this.symm
  refine ⟨hSv, substAlg T p, ?_, dvd_substAlg_of_dvd h1 hD hpdvd, ?_, ?_⟩
  · exact (irreducible_substAlg_iff h2 h1 p).mpr hpirr
  · have hback : substAlg S (substAlg T p) = p := by rw [substAlg_comp, h2, substAlg_one]
    rw [← eval_substAlg, hback]
    exact hpev
  · intro q hqirr hqdvd hqna
    have hqP : substAlg S q ∣ DP := dvd_of_dvd_substAlg hκ hD hqdvd
    have hqirr' : Irreducible (substAlg S q) := (irreducible_substAlg_iff h1 h2 q).mpr hqirr
    have hna : ¬ Associated (substAlg S q) p := by
      intro hcon
      apply hqna
      have hback : substAlg S (substAlg T p) = p := by rw [substAlg_comp, h2, substAlg_one]
      rw [← hback] at hcon
      exact (associated_substAlg_iff h1 q (substAlg T p)).mp hcon
    have := hother _ hqirr' hqP hna
    rwa [eval_substAlg] at this

omit hκ hD in
/-- Transport of the component splitting field `def:splittingfield`. -/
lemma allFactorsDefinedOver_of (E : Subfield Ω) (hT : ∀ i j, T i j ∈ E)
    (hκ : κ ≠ 0) (hD : substAlg S DQ = C κ * DP) (hP : AllFactorsDefinedOver E DP) :
    AllFactorsDefinedOver E DQ := by
  intro p hpirr hpdvd
  obtain ⟨u, hu0, hu⟩ := hP (substAlg S p) ((irreducible_substAlg_iff h1 h2 p).mpr hpirr)
    (dvd_of_dvd_substAlg hκ hD hpdvd)
  refine ⟨u, hu0, ?_⟩
  have hback : substAlg T (C u * substAlg S p) = C u * p := by
    rw [map_mul, algHom_C, substAlg_comp, h1, substAlg_one, algebraMap_eq]
  rw [← hback]
  exact substAlg_mem_coeffsIn hT hu

/-- The determinant vertices of the two forms correspond under the substitution. -/
lemma isDetVertex_iff (v : Fin n → Ω) : IsDetVertex DP v ↔ IsDetVertex DQ (S.mulVec v) := by
  refine ⟨isDetVertex_of_isDetVertex h1 h2 hκ hD v, fun hv => ?_⟩
  have h := isDetVertex_of_isDetVertex h2 h1 (inv_ne_zero hκ)
    (substAlg_symm h1 hκ hD) (S.mulVec v) hv
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h

/-- **Invariance of the component splitting field** `def:splittingfield` under an invertible
substitution defined over `K'` together with a nonzero scalar factor. -/
theorem componentField_transport (K' : Subfield Ω) (hS : ∀ i j, S i j ∈ K')
    (hT : ∀ i j, T i j ∈ K') : componentField K' DP = componentField K' DQ := by
  have hset : {E : Subfield Ω | K' ≤ E ∧ AllFactorsDefinedOver E DP}
      = {E : Subfield Ω | K' ≤ E ∧ AllFactorsDefinedOver E DQ} := by
    ext E
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hKE, hP⟩
      exact ⟨hKE, allFactorsDefinedOver_of h1 h2 E (fun i j => hKE (hT i j)) hκ hD hP⟩
    · rintro ⟨hKE, hQ⟩
      exact ⟨hKE, allFactorsDefinedOver_of h2 h1 E (fun i j => hKE (hS i j)) (inv_ne_zero hκ)
        (substAlg_symm h1 hκ hD) hQ⟩
  unfold componentField
  rw [hset]

/-- **Invariance of the degrees of the absolutely irreducible components.** -/
theorem absFactorDegrees_transport : absFactorDegrees DP = absFactorDegrees DQ := by
  ext d
  constructor
  · rintro ⟨p, hpirr, hpdvd, hdeg⟩
    exact ⟨substAlg T p, (irreducible_substAlg_iff h2 h1 p).mpr hpirr,
      dvd_substAlg_of_dvd h1 hD hpdvd, by rw [substAlg_totalDegree h2, hdeg]⟩
  · rintro ⟨p, hpirr, hpdvd, hdeg⟩
    exact ⟨substAlg S p, (irreducible_substAlg_iff h1 h2 p).mpr hpirr,
      dvd_of_dvd_substAlg hκ hD hpdvd, by rw [substAlg_totalDegree h1, hdeg]⟩

/-- **Invariance of the extended determinant-vertex rank** `eq:vertexinvariant`. -/
theorem vertexRanks_transport (MP MQ : (Fin n → Ω) → Matrix (Fin n) (Fin n) Ω)
    (hrank : ∀ v, (MQ (S.mulVec v)).rank = (MP v).rank) :
    vertexRanks DP MP = vertexRanks DQ MQ := by
  ext r
  constructor
  · rintro ⟨v, hv, hr⟩
    exact ⟨S.mulVec v, (isDetVertex_iff h1 h2 hκ hD v).mp hv, by rw [hrank v, hr]⟩
  · rintro ⟨u, hu, hr⟩
    refine ⟨T.mulVec u, ?_, ?_⟩
    · rw [isDetVertex_iff h1 h2 hκ hD, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      exact hu
    · rw [← hrank (T.mulVec u), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, hr]

end Transport

section KLinear

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {n : ℕ}

/-- The left determinant form, read over the extension field `Ω`. -/
noncomputable def detFormLE (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) Ω :=
  (detFormL c).map (algebraMap K Ω)

/-- The right determinant form, read over the extension field `Ω`. -/
noncomputable def detFormRE (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) Ω :=
  (detFormR c).map (algebraMap K Ω)

/-- The transpose determinant form, read over the extension field `Ω`. -/
noncomputable def detFormTE (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) Ω :=
  (detFormT c).map (algebraMap K Ω)

lemma map_substHom (S : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin n) K) :
    (substHom S p).map (algebraMap K Ω)
      = substAlg (S.map (algebraMap K Ω)) (p.map (algebraMap K Ω)) := by
  have h : ((MvPolynomial.map (algebraMap K Ω) : MvPolynomial (Fin n) K →+* _).comp
        (substHom S : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K))
      = ((substAlg (S.map (algebraMap K Ω)) :
            MvPolynomial (Fin n) Ω →+* MvPolynomial (Fin n) Ω).comp
          (MvPolynomial.map (algebraMap K Ω))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [substHom_X]
  exact congrArg (fun f => f p) h

lemma actOn_eq_mulVec (S : Matrix (Fin n) (Fin n) K) (v : Fin n → Ω) :
    actOn S v = (S.map (algebraMap K Ω)).mulVec v := by
  funext i
  simp [actOn, Matrix.mulVec, dotProduct]

variable {mulP mulQ : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)}

/-- The matrices of an invertible `K`-linear map and of its inverse are mutually inverse. -/
lemma matOf_mul_matOf_symm (A : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    matOf (A : (Fin n → K) →ₗ[K] (Fin n → K)) * matOf (A.symm : _ →ₗ[K] _) = 1 := by
  rw [← matOf_comp]
  have hid : ((A : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (A.symm : _ →ₗ[K] _)) = LinearMap.id := by
    ext x; simp
  rw [hid, matOf_id]

lemma matOf_symm_mul_matOf (A : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    matOf (A.symm : (Fin n → K) →ₗ[K] (Fin n → K)) * matOf (A : _ →ₗ[K] _) = 1 := by
  rw [← matOf_comp]
  have hid : ((A.symm : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (A : _ →ₗ[K] _)) = LinearMap.id := by
    ext x; simp
  rw [hid, matOf_id]

lemma det_matOf_ne_zero (A : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := by
  intro h
  have := isUnit_det_matOf A
  rw [h] at this
  exact not_isUnit_zero this

private lemma substAlg_eq_of_mul {S : Matrix (Fin n) (Fin n) Ω} {DP DQ : MvPolynomial (Fin n) Ω}
    {b c : Ω} (hb : b ≠ 0) (h : substAlg S DQ * C b = C c * DP) :
    substAlg S DQ = C (c * b⁻¹) * DP := by
  have h' := congrArg (fun p => p * C b⁻¹) h
  simp only at h'
  rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hb, C_1, mul_one] at h'
  rw [h', C_mul]
  ring

variable (A B Cm : (Fin n → K) ≃ₗ[K] (Fin n → K))

/-- **`thm:invariance`, left determinant, `K`-linear case.**  A `K`-linear isotopism preserves
the component splitting field, the degrees of the absolutely irreducible components and the
extended determinant-vertex rank of the left determinant form. -/
theorem profile_invariance_left
    (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (K' : Subfield Ω)
    (hK' : ∀ a : K, algebraMap K Ω a ∈ K') :
    componentField K' (detFormLE (Ω := Ω) (structTensor mulP))
        = componentField K' (detFormLE (Ω := Ω) (structTensor mulQ)) ∧
      absFactorDegrees (detFormLE (Ω := Ω) (structTensor mulP))
        = absFactorDegrees (detFormLE (Ω := Ω) (structTensor mulQ)) ∧
      vertexRanks (detFormLE (Ω := Ω) (structTensor mulP))
          (pencilLat (Ω := Ω) (structTensor mulP))
        = vertexRanks (detFormLE (Ω := Ω) (structTensor mulQ))
          (pencilLat (Ω := Ω) (structTensor mulQ)) := by
  classical
  set S : Matrix (Fin n) (Fin n) Ω :=
    (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).map (algebraMap K Ω) with hS
  set T : Matrix (Fin n) (Fin n) Ω :=
    (matOf (A.symm : (Fin n → K) →ₗ[K] (Fin n → K))).map (algebraMap K Ω) with hT
  have h1 : S * T = 1 := by
    rw [hS, hT, ← Matrix.map_mul, matOf_mul_matOf_symm A]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have h2 : T * S = 1 := by
    rw [hS, hT, ← Matrix.map_mul, matOf_symm_mul_matOf A]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have hbK : (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero B
  have hcK : (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero Cm
  have hb : algebraMap K Ω (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr hbK
  have hc : algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr hcK
  have hLK := detFormL_isotopy (A := (A : (Fin n → K) →ₗ[K] (Fin n → K)))
    (B := (B : (Fin n → K) →ₗ[K] (Fin n → K)))
    (Cm := (Cm : (Fin n → K) →ₗ[K] (Fin n → K))) hiso
  have hL := congrArg (MvPolynomial.map (algebraMap K Ω)) hLK
  rw [map_mul, map_mul, map_substHom, MvPolynomial.map_C, MvPolynomial.map_C] at hL
  have hD : substAlg S (detFormLE (Ω := Ω) (structTensor mulQ))
      = C (algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det
            * (algebraMap K Ω (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det)⁻¹)
          * detFormLE (Ω := Ω) (structTensor mulP) :=
    substAlg_eq_of_mul hb hL
  have hκ : algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det
      * (algebraMap K Ω (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det)⁻¹ ≠ 0 :=
    mul_ne_zero hc (inv_ne_zero hb)
  have hrank : ∀ v : Fin n → Ω, (pencilLat (Ω := Ω) (structTensor mulQ) (S.mulVec v)).rank
      = (pencilLat (Ω := Ω) (structTensor mulP) v).rank := by
    intro v
    rw [hS, ← actOn_eq_mulVec]
    exact rank_pencilLat_isotopy hiso (isUnit_det_matOf B) (isUnit_det_matOf Cm) v
  refine ⟨componentField_transport h1 h2 hκ hD K' (fun i j => hK' _) (fun i j => hK' _),
    absFactorDegrees_transport h1 h2 hκ hD, vertexRanks_transport h1 h2 hκ hD _ _ hrank⟩

/-- **`thm:invariance`, right determinant, `K`-linear case.** -/
theorem profile_invariance_right
    (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (K' : Subfield Ω)
    (hK' : ∀ a : K, algebraMap K Ω a ∈ K') :
    componentField K' (detFormRE (Ω := Ω) (structTensor mulP))
        = componentField K' (detFormRE (Ω := Ω) (structTensor mulQ)) ∧
      absFactorDegrees (detFormRE (Ω := Ω) (structTensor mulP))
        = absFactorDegrees (detFormRE (Ω := Ω) (structTensor mulQ)) ∧
      vertexRanks (detFormRE (Ω := Ω) (structTensor mulP))
          (pencilRat (Ω := Ω) (structTensor mulP))
        = vertexRanks (detFormRE (Ω := Ω) (structTensor mulQ))
          (pencilRat (Ω := Ω) (structTensor mulQ)) := by
  classical
  set S : Matrix (Fin n) (Fin n) Ω :=
    (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).map (algebraMap K Ω) with hS
  set T : Matrix (Fin n) (Fin n) Ω :=
    (matOf (B.symm : (Fin n → K) →ₗ[K] (Fin n → K))).map (algebraMap K Ω) with hT
  have h1 : S * T = 1 := by
    rw [hS, hT, ← Matrix.map_mul, matOf_mul_matOf_symm B]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have h2 : T * S = 1 := by
    rw [hS, hT, ← Matrix.map_mul, matOf_symm_mul_matOf B]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have haK : (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero A
  have hcK : (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero Cm
  have ha : algebraMap K Ω (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr haK
  have hc : algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr hcK
  have hRK := detFormR_isotopy (A := (A : (Fin n → K) →ₗ[K] (Fin n → K)))
    (B := (B : (Fin n → K) →ₗ[K] (Fin n → K)))
    (Cm := (Cm : (Fin n → K) →ₗ[K] (Fin n → K))) hiso
  have hR := congrArg (MvPolynomial.map (algebraMap K Ω)) hRK
  rw [map_mul, map_mul, map_substHom, MvPolynomial.map_C, MvPolynomial.map_C] at hR
  have hD : substAlg S (detFormRE (Ω := Ω) (structTensor mulQ))
      = C (algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det
            * (algebraMap K Ω (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det)⁻¹)
          * detFormRE (Ω := Ω) (structTensor mulP) :=
    substAlg_eq_of_mul ha hR
  have hκ : algebraMap K Ω (matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).det
      * (algebraMap K Ω (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det)⁻¹ ≠ 0 :=
    mul_ne_zero hc (inv_ne_zero ha)
  have hrank : ∀ v : Fin n → Ω, (pencilRat (Ω := Ω) (structTensor mulQ) (S.mulVec v)).rank
      = (pencilRat (Ω := Ω) (structTensor mulP) v).rank := by
    intro v
    rw [hS, ← actOn_eq_mulVec]
    exact rank_pencilRat_isotopy hiso (isUnit_det_matOf A) (isUnit_det_matOf Cm) v
  refine ⟨componentField_transport h1 h2 hκ hD K' (fun i j => hK' _) (fun i j => hK' _),
    absFactorDegrees_transport h1 h2 hκ hD, vertexRanks_transport h1 h2 hκ hD _ _ hrank⟩

/-- **`thm:invariance`, transpose determinant, `K`-linear case.** -/
theorem profile_invariance_transpose
    (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (K' : Subfield Ω)
    (hK' : ∀ a : K, algebraMap K Ω a ∈ K') :
    componentField K' (detFormTE (Ω := Ω) (structTensor mulP))
        = componentField K' (detFormTE (Ω := Ω) (structTensor mulQ)) ∧
      absFactorDegrees (detFormTE (Ω := Ω) (structTensor mulP))
        = absFactorDegrees (detFormTE (Ω := Ω) (structTensor mulQ)) ∧
      vertexRanks (detFormTE (Ω := Ω) (structTensor mulP))
          (pencilTat (Ω := Ω) (structTensor mulP))
        = vertexRanks (detFormTE (Ω := Ω) (structTensor mulQ))
          (pencilTat (Ω := Ω) (structTensor mulQ)) := by
  classical
  set S : Matrix (Fin n) (Fin n) Ω :=
    ((matOf (Cm : (Fin n → K) →ₗ[K] (Fin n → K))).transpose).map (algebraMap K Ω) with hS
  set T : Matrix (Fin n) (Fin n) Ω :=
    ((matOf (Cm.symm : (Fin n → K) →ₗ[K] (Fin n → K))).transpose).map (algebraMap K Ω) with hT
  have h1 : S * T = 1 := by
    rw [hS, hT, ← Matrix.map_mul, ← Matrix.transpose_mul, matOf_symm_mul_matOf Cm,
      Matrix.transpose_one]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have h2 : T * S = 1 := by
    rw [hS, hT, ← Matrix.map_mul, ← Matrix.transpose_mul, matOf_mul_matOf_symm Cm,
      Matrix.transpose_one]
    simp [Matrix.map_one (algebraMap K Ω) (map_zero _) (map_one _)]
  have haK : (matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero A
  have hbK : (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0 := det_matOf_ne_zero B
  have hab : algebraMap K Ω ((matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det
      * (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr (mul_ne_zero haK hbK)
  have hTK := detFormT_isotopy (A := (A : (Fin n → K) →ₗ[K] (Fin n → K)))
    (B := (B : (Fin n → K) →ₗ[K] (Fin n → K)))
    (Cm := (Cm : (Fin n → K) →ₗ[K] (Fin n → K))) hiso
  have hTr := congrArg (MvPolynomial.map (algebraMap K Ω)) hTK
  rw [map_substHom, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C] at hTr
  have hD : substAlg S (detFormTE (Ω := Ω) (structTensor mulP))
      = C (algebraMap K Ω ((matOf (A : (Fin n → K) →ₗ[K] (Fin n → K))).det
            * (matOf (B : (Fin n → K) →ₗ[K] (Fin n → K))).det))
          * detFormTE (Ω := Ω) (structTensor mulQ) := by
    simp only [detFormTE, hS]
    rw [hTr, map_mul, C_mul]
    ring
  have hrank : ∀ v : Fin n → Ω, (pencilTat (Ω := Ω) (structTensor mulP) (S.mulVec v)).rank
      = (pencilTat (Ω := Ω) (structTensor mulQ) v).rank := by
    intro v
    rw [hS, ← actOn_eq_mulVec]
    exact rank_pencilTat_isotopy hiso (isUnit_det_matOf A) (isUnit_det_matOf B) v
  exact ⟨(componentField_transport h1 h2 hab hD K' (fun i j => hK' _) (fun i j => hK' _)).symm,
    (absFactorDegrees_transport h1 h2 hab hD).symm,
    (vertexRanks_transport h1 h2 hab hD _ _ hrank).symm⟩

end KLinear

end Semifields
