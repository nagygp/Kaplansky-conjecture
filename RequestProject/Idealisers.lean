import RequestProject.Nuclei

/-!
# The idealisers of the spread sets of the family (`thm:direct-nuclei`)

This file evaluates the coefficient functions `e1`, `e2`, `e3` of
`RequestProject.Nuclei` at the positions used in the proof of `thm:direct-nuclei`, and
deduces the three idealiser computations

`I_l(𝒞^d) = I_l(𝒞) = I_r(𝒞) = {m_a : a ∈ K}`.
-/

namespace Semifields

open scoped BigOperators

section Evaluations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

variable (hn5 : 5 ≤ n)
include hn5

omit [NeZero n] in
lemma e3_at_add_one (c : ZMod n → F) (i : ZMod n) :
    e3 w c i (i + 1) = c (i - 1) + c (i + 2) := by
  obtain ⟨z1, z2, z3, -⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ (i + 1 = i - 2) := fun hh => z3 (by linear_combination hh)
  have c2 : ¬ (i + 1 = i - 1) := fun hh => z2 (by linear_combination hh)
  have c3 : ¬ (i + 1 = i + 2) := fun hh => z1 (by linear_combination -hh)
  simp only [e3, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e3_at_sub_two (c : ZMod n → F) (i : ZMod n) :
    e3 w c i (i - 2) = c (i - 1) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ (i - 2 = i + 1) := fun hh => z3 (by linear_combination -hh)
  have c2 : ¬ (i - 2 = i - 1) := fun hh => z1 (by linear_combination -hh)
  have c3 : ¬ (i - 2 = i + 2) := fun hh => z4 (by linear_combination -hh)
  simp only [e3, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e3_at_sub_one (c : ZMod n → F) (i : ZMod n) :
    e3 w c i (i - 1) = algebraMap K F w * (c (i - 2) + c (i + 1)) := by
  obtain ⟨z1, z2, z3, -⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ (i - 1 = i + 1) := fun hh => z2 (by linear_combination -hh)
  have c2 : ¬ (i - 1 = i - 2) := fun hh => z1 (by linear_combination hh)
  have c3 : ¬ (i - 1 = i + 2) := fun hh => z3 (by linear_combination -hh)
  simp only [e3, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e3_at_add_two (c : ZMod n → F) (i : ZMod n) :
    e3 w c i (i + 2) = algebraMap K F w * c (i + 1) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ (i + 2 = i + 1) := fun hh => z1 (by linear_combination hh)
  have c2 : ¬ (i + 2 = i - 2) := fun hh => z4 (by linear_combination hh)
  have c3 : ¬ (i + 2 = i - 1) := fun hh => z3 (by linear_combination hh)
  simp only [e3, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] hn5 in
/-- Off the four exponents `{1, 2, -1, -2}` the left-hand coefficients vanish. -/
lemma e1_eq_zero_of_notMem {j : ZMod n} (h1 : j ≠ 1) (h2 : j ≠ 2) (hm1 : j ≠ -1)
    (hm2 : j ≠ -2) (a : ZMod n → F) (i : ZMod n) : e1 σ w a i j = 0 := by
  simp only [e1, if_neg h1, if_neg h2, if_neg hm1, if_neg hm2]
  simp

omit [NeZero n] in
lemma e1_at_two (a : ZMod n → F) (i : ZMod n) :
    e1 σ w a i (2 : ZMod n) = sig σ (1 : ZMod n) (a (i - 1)) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((2 : ZMod n) = -1) := fun hh => z3 (by linear_combination hh)
  have c2 : ¬ ((2 : ZMod n) = 1) := fun hh => z1 (by linear_combination hh)
  have c3 : ¬ ((2 : ZMod n) = -2) := fun hh => z4 (by linear_combination hh)
  simp only [e1, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e1_at_neg_two (a : ZMod n → F) (i : ZMod n) :
    e1 σ w a i (-2 : ZMod n) = algebraMap K F w * sig σ (-1 : ZMod n) (a (i + 1)) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((-2 : ZMod n) = 2) := fun hh => z4 (by linear_combination -hh)
  have c2 : ¬ ((-2 : ZMod n) = -1) := fun hh => z1 (by linear_combination -hh)
  have c3 : ¬ ((-2 : ZMod n) = 1) := fun hh => z3 (by linear_combination -hh)
  simp only [e1, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] hn5 in
/-- Off the four exponents `{1, 2, -1, -2}` in the first variable the right-hand
coefficients vanish. -/
lemma e2_eq_zero_of_notMem {i : ZMod n} (h1 : i ≠ 1) (h2 : i ≠ 2) (hm1 : i ≠ -1)
    (hm2 : i ≠ -2) (b : ZMod n → F) (j : ZMod n) : e2 σ w b i j = 0 := by
  simp only [e2, if_neg h1, if_neg h2, if_neg hm1, if_neg hm2]
  simp

omit [NeZero n] in
lemma e2_at_one (b : ZMod n → F) (j : ZMod n) :
    e2 σ w b (1 : ZMod n) j
      = sig σ (2 : ZMod n) (b (j - 2)) + sig σ (-1 : ZMod n) (b (j + 1)) := by
  obtain ⟨z1, z2, z3, -⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((1 : ZMod n) = -2) := fun hh => z3 (by linear_combination hh)
  have c2 : ¬ ((1 : ZMod n) = 2) := fun hh => z1 (by linear_combination -hh)
  have c3 : ¬ ((1 : ZMod n) = -1) := fun hh => z2 (by linear_combination hh)
  simp only [e2, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e2_at_neg_two (b : ZMod n → F) (j : ZMod n) :
    e2 σ w b (-2 : ZMod n) j = sig σ (-1 : ZMod n) (b (j + 1)) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((-2 : ZMod n) = 1) := fun hh => z3 (by linear_combination -hh)
  have c2 : ¬ ((-2 : ZMod n) = 2) := fun hh => z4 (by linear_combination -hh)
  have c3 : ¬ ((-2 : ZMod n) = -1) := fun hh => z1 (by linear_combination -hh)
  simp only [e2, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e2_at_two (b : ZMod n → F) (j : ZMod n) :
    e2 σ w b (2 : ZMod n) j = algebraMap K F w * sig σ (1 : ZMod n) (b (j - 1)) := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((2 : ZMod n) = 1) := fun hh => z1 (by linear_combination hh)
  have c2 : ¬ ((2 : ZMod n) = -2) := fun hh => z4 (by linear_combination hh)
  have c3 : ¬ ((2 : ZMod n) = -1) := fun hh => z3 (by linear_combination hh)
  simp only [e2, if_neg c1, if_neg c2, if_neg c3]
  simp

omit [NeZero n] in
lemma e2_at_neg_one (b : ZMod n → F) (j : ZMod n) :
    e2 σ w b (-1 : ZMod n) j
      = algebraMap K F w * (sig σ (1 : ZMod n) (b (j - 1)) + sig σ (-2 : ZMod n) (b (j + 2))) := by
  obtain ⟨z1, z2, -, -⟩ := zmod_small_facts (n := n) hn5
  obtain ⟨-, -, z3, -⟩ := zmod_small_facts (n := n) hn5
  have c1 : ¬ ((-1 : ZMod n) = 1) := fun hh => z2 (by linear_combination -hh)
  have c2 : ¬ ((-1 : ZMod n) = -2) := fun hh => z1 (by linear_combination hh)
  have c3 : ¬ ((-1 : ZMod n) = 2) := fun hh => z3 (by linear_combination -hh)
  simp only [e2, if_neg c1, if_neg c2, if_neg c3]
  simp

end Evaluations

section GaloisFixed

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F}

/-- If `a` is fixed by `σ ^ d` then it is fixed by `σ ^ (d * m)` for every `m`. -/
lemma sig_fixed_mul (hσ : σ ^ n = 1) {a : F} {d : ZMod n} (ha : sig σ d a = a) :
    ∀ m : ZMod n, sig σ (d * m) a = a := by
  have hnat : ∀ k : ℕ, sig σ (d * (k : ZMod n)) a = a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : d * ((k + 1 : ℕ) : ZMod n) = d * (k : ZMod n) + d := by push_cast; ring
      rw [hstep, sig_add_apply hσ, ha, ih]
  intro m
  have hm : ((m.val : ℕ) : ZMod n) = m := ZMod.natCast_zmod_val m
  rw [← hm]
  exact hnat m.val

omit [NeZero n] in
/-- An element fixed by every power of `σ` lies in the base field, when the powers of `σ`
exhaust the Galois group. -/
lemma mem_range_algebraMap_of_sig_fixed [FiniteDimensional K F] [IsGalois K F]
    (hσgen : Function.Bijective (fun i : ZMod n => sig σ i)) {a : F}
    (h : ∀ i : ZMod n, sig σ i a = a) : ∃ k : K, algebraMap K F k = a := by
  have htfae := IsGalois.tfae (F := K) (E := F)
  have hfix : IntermediateField.fixedField ⊤ = ⊥ := (htfae.out 0 1).mp ‹IsGalois K F›
  have hmem : a ∈ IntermediateField.fixedField (⊤ : Subgroup (F ≃ₐ[K] F)) := by
    intro f
    obtain ⟨i, hi⟩ := hσgen.surjective (f : F ≃ₐ[K] F)
    show (f : F ≃ₐ[K] F) a = a
    rw [← hi]
    exact h i
  rw [hfix] at hmem
  exact IntermediateField.mem_bot.mp hmem

/-- An element fixed by `σ ^ d`, for `d` a unit modulo `n`, lies in the base field. -/
lemma mem_range_algebraMap_of_unit_fixed [FiniteDimensional K F] [IsGalois K F]
    (hσgen : Function.Bijective (fun i : ZMod n => sig σ i)) (hσ : σ ^ n = 1)
    {a : F} {d : ZMod n} (hd : IsUnit d) (ha : sig σ d a = a) :
    ∃ k : K, algebraMap K F k = a := by
  refine mem_range_algebraMap_of_sig_fixed hσgen (fun i => ?_)
  obtain ⟨u, hu⟩ := hd.exists_right_inv
  have hi : d * (u * i) = i := by rw [← mul_assoc, hu, one_mul]
  rw [← hi]
  exact sig_fixed_mul hσ ha (u * i)

end GaloisFixed


section SigZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F}

omit [NeZero n] in
lemma sig_eq_zero {i : ZMod n} {z : F} (h : sig σ i z = 0) : z = 0 := by
  have h2 := congrArg (fun t => (sig σ i).symm t) h
  simpa using h2

end SigZero


section Main

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

variable (hsgen : Function.Bijective (fun i : ZMod n => sig σ i)) (hfin : Module.finrank K F = n)
  (hsn : σ ^ n = 1) (hn5 : 5 ≤ n) (hcop : Nat.Coprime 4 n) (hcop2 : Nat.Coprime 2 n)
  (hw : w ^ 2 - w + 1 = 0) (hP : IsPresemifield K (famMulₗ n σ w))
include hsgen hfin hsn hn5 hcop hcop2 hw hP

/-- **`thm:direct-nuclei`, first idealiser.**  The left idealiser of the dual spread set of
the family is the set of `K`-scalar multiplications. -/
theorem leftIdealiser_famCd_eq : leftIdealiser (famCd n σ w) = scalarMaps K F := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; norm_num at hw
  have hwF : algebraMap K F w ≠ 0 := fun h =>
    hw0 ((algebraMap K F).injective (by simpa using h))
  have h2unit : IsUnit (2 : ZMod n) := by
    have h22 : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
    rw [← h22, ZMod.isUnit_iff_coprime]; exact hcop2
  ext T
  simp only [scalarMaps, Set.mem_setOf_eq, mem_leftIdealiser_famCd]
  constructor
  · intro hT
    choose A hA using hT
    have hTsmul : ∀ (k : K) (z : F), T (algebraMap K F k * z) = algebraMap K F k * T z := by
      intro k z
      obtain ⟨y, hy⟩ := famMul_right_surjective hP (x := 1) one_ne_zero z
      simp only at hy
      rw [← hy, ← famMul_smul_right, hA, hA, famMul_smul_right]
    let Tl : F →ₗ[K] F :=
      { toFun := T, map_add' := T.map_add,
        map_smul' := by
          intro k z
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hTsmul k z }
    have hAadd : ∀ x₁ x₂, A (x₁ + x₂) = A x₁ + A x₂ := by
      intro x₁ x₂
      refine famMul_left_cancel hP (fun y => ?_)
      rw [← hA, famMul_add_left, map_add, hA, hA, ← famMul_add_left]
    have hAsmul : ∀ (k : K) (x : F), A (algebraMap K F k * x) = algebraMap K F k * A x := by
      intro k x
      refine famMul_left_cancel hP (fun y => ?_)
      rw [← hA, famMul_smul_left, hTsmul, hA, famMul_smul_left]
    let Al : F →ₗ[K] F :=
      { toFun := A, map_add' := hAadd,
        map_smul' := by
          intro k x
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hAsmul k x }
    obtain ⟨a, ha⟩ := exists_sig_expansion hsgen.injective hfin Al
    obtain ⟨c, hc⟩ := exists_sig_expansion hsgen.injective hfin Tl
    have ha' : ∀ x, A x = lp σ a x := fun x => ha x
    have hc' : ∀ z, T z = lp σ c z := fun z => hc z
    have hcoef : ∀ i j, e1 σ w a i j = e3 w c i j := by
      have hzero : ∀ x y : F,
          ∑ i, ∑ j, (e1 σ w a i j - e3 w c i j) * (sig σ i x * sig σ j y) = 0 := by
        intro x y
        have hsplit : ∑ i, ∑ j, (e1 σ w a i j - e3 w c i j) * (sig σ i x * sig σ j y)
            = (∑ i, ∑ j, e1 σ w a i j * (sig σ i x * sig σ j y))
              - ∑ i, ∑ j, e3 w c i j * (sig σ i x * sig σ j y) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit, ← expand_e1 hsn a x y, ← expand_e3 hsn c x y, ← ha', ← hc', hA, sub_self]
      intro i j
      exact sub_eq_zero.mp (sig_bilinear_coeff_eq_zero hsgen.injective
        (fun i j => e1 σ w a i j - e3 w c i j) hzero i j)
    have hcsupp : ∀ m : ZMod n, m ≠ 0 → c m = 0 := by
      refine support_at_zero hn5 hcop c ?_
      rintro j ⟨hj1, hj2, hjm1, hjm2⟩
      have hz : ∀ i, e3 w c i j = 0 := fun i => by
        rw [← hcoef i j]
        exact e1_eq_zero_of_notMem hj1 hj2 hjm1 hjm2 a i
      have E2 := e3_at_sub_two (w := w) hn5 c (j + 2)
      rw [show j + 2 - 2 = j from by ring, show j + 2 - 1 = j + 1 from by ring] at E2
      have k1 : c (j + 1) = 0 := by rw [← E2]; exact hz (j + 2)
      have E1 := e3_at_add_two (w := w) hn5 c (j - 2)
      rw [show j - 2 + 2 = j from by ring, show j - 2 + 1 = j - 1 from by ring] at E1
      have k3 : c (j - 1) = 0 := by
        have hh := hz (j - 2)
        rw [E1] at hh
        exact (mul_eq_zero.mp hh).resolve_left hwF
      have E3 := e3_at_add_one (w := w) hn5 c (j - 1)
      rw [show j - 1 + 1 = j from by ring, show j - 1 - 1 = j - 2 from by ring,
        show j - 1 + 2 = j + 1 from by ring] at E3
      have k4 : c (j - 2) = 0 := by
        have hh := hz (j - 1)
        rw [E3, k1, add_zero] at hh
        exact hh
      have E4 := e3_at_sub_one (w := w) hn5 c (j + 1)
      rw [show j + 1 - 1 = j from by ring, show j + 1 - 2 = j - 1 from by ring,
        show j + 1 + 1 = j + 2 from by ring] at E4
      have k2 : c (j + 2) = 0 := by
        have hh := hz (j + 1)
        rw [E4, k3, zero_add] at hh
        exact (mul_eq_zero.mp hh).resolve_left hwF
      exact ⟨k1, k2, k3, k4⟩
    have hac : sig σ (1 : ZMod n) (a 0) = c 0 := by
      have h := hcoef 1 2
      rw [e1_at_two hn5, show (1 : ZMod n) - 1 = 0 from by ring] at h
      have E := e3_at_add_one (w := w) hn5 c (1 : ZMod n)
      rw [show (1 : ZMod n) + 1 = 2 from by ring, show (1 : ZMod n) - 1 = 0 from by ring,
        show (1 : ZMod n) + 2 = 3 from by ring] at E
      rw [E, hcsupp 3 z3, add_zero] at h
      exact h
    have hac2 : sig σ (-1 : ZMod n) (a 0) = c 0 := by
      have h := hcoef (-1) (-2)
      rw [e1_at_neg_two hn5, show (-1 : ZMod n) + 1 = 0 from by ring] at h
      have E := e3_at_sub_one (w := w) hn5 c (-1 : ZMod n)
      rw [show (-1 : ZMod n) - 1 = -2 from by ring, show (-1 : ZMod n) - 2 = -3 from by ring,
        show (-1 : ZMod n) + 1 = 0 from by ring] at E
      rw [E, hcsupp (-3) (fun hh => z3 (by linear_combination -hh)), zero_add] at h
      exact mul_left_cancel₀ hwF h
    have hfix : sig σ (2 : ZMod n) (a 0) = a 0 := by
      have e := hac.trans hac2.symm
      have h2 := congrArg (fun t => sig σ (1 : ZMod n) t) e
      simp only at h2
      rw [← sig_add_apply hsn, ← sig_add_apply hsn] at h2
      rw [show (1 : ZMod n) + 1 = 2 from by ring, show (1 : ZMod n) + -1 = 0 from by ring] at h2
      simpa using h2
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_unit_fixed hsgen hsn h2unit hfix
    refine ⟨k, fun z => ?_⟩
    have hsum : ∑ i, c i * sig σ i z = c 0 * sig σ (0 : ZMod n) z :=
      Finset.sum_eq_single (0 : ZMod n) (fun i _ hi => by rw [hcsupp i hi, zero_mul])
        (fun hcon => absurd (Finset.mem_univ _) hcon)
    rw [hc' z, lp, hsum, ← hac, ← hk, sig_algebraMap]
    simp
  · rintro ⟨k, hk⟩ x
    exact ⟨algebraMap K F k * x, fun y => by rw [hk, famMul_smul_left]⟩

/-- **`thm:direct-nuclei`, third idealiser.**  The right idealiser of the spread set of the
family is the set of `K`-scalar multiplications. -/
theorem rightIdealiser_famC_eq : rightIdealiser (famC n σ w) = scalarMaps K F := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; norm_num at hw
  have hwF : algebraMap K F w ≠ 0 := fun h =>
    hw0 ((algebraMap K F).injective (by simpa using h))
  have h2unit : IsUnit (2 : ZMod n) := by
    have h22 : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
    rw [← h22, ZMod.isUnit_iff_coprime]; exact hcop2
  ext T
  simp only [scalarMaps, Set.mem_setOf_eq, mem_rightIdealiser_famC]
  constructor
  · intro hT
    choose B hB using hT
    have hTsmul : ∀ (k : K) (x : F), T (algebraMap K F k * x) = algebraMap K F k * T x := by
      intro k x
      refine famMul_left_cancel hP (fun y => ?_)
      rw [hB, famMul_smul_left, ← hB, famMul_smul_left]
    let Tl : F →ₗ[K] F :=
      { toFun := T, map_add' := T.map_add,
        map_smul' := by
          intro k x
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hTsmul k x }
    have hBadd : ∀ y₁ y₂, B (y₁ + y₂) = B y₁ + B y₂ := by
      intro y₁ y₂
      refine famMul_right_cancel hP (fun x => ?_)
      rw [← hB, famMul_add_right, hB, hB, ← famMul_add_right]
    have hBsmul : ∀ (k : K) (y : F), B (algebraMap K F k * y) = algebraMap K F k * B y := by
      intro k y
      refine famMul_right_cancel hP (fun x => ?_)
      rw [← hB, famMul_smul_right, hB, famMul_smul_right]
    let Bl : F →ₗ[K] F :=
      { toFun := B, map_add' := hBadd,
        map_smul' := by
          intro k y
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hBsmul k y }
    obtain ⟨a, ha⟩ := exists_sig_expansion hsgen.injective hfin Tl
    obtain ⟨b, hb⟩ := exists_sig_expansion hsgen.injective hfin Bl
    have ha' : ∀ x, T x = lp σ a x := fun x => ha x
    have hb' : ∀ y, B y = lp σ b y := fun y => hb y
    have hcoef : ∀ i j, e1 σ w a i j = e2 σ w b i j := by
      have hzero : ∀ x y : F,
          ∑ i, ∑ j, (e1 σ w a i j - e2 σ w b i j) * (sig σ i x * sig σ j y) = 0 := by
        intro x y
        have hsplit : ∑ i, ∑ j, (e1 σ w a i j - e2 σ w b i j) * (sig σ i x * sig σ j y)
            = (∑ i, ∑ j, e1 σ w a i j * (sig σ i x * sig σ j y))
              - ∑ i, ∑ j, e2 σ w b i j * (sig σ i x * sig σ j y) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit, ← expand_e1 hsn a x y, ← expand_e2 hsn b x y, ← ha', ← hb', hB, sub_self]
      intro i j
      exact sub_eq_zero.mp (sig_bilinear_coeff_eq_zero hsgen.injective
        (fun i j => e1 σ w a i j - e2 σ w b i j) hzero i j)
    have hbsupp : ∀ m : ZMod n, m ≠ 0 → b m = 0 := by
      refine support_at_zero hn5 hcop b ?_
      rintro j ⟨hj1, hj2, hjm1, hjm2⟩
      have hz : ∀ i, e2 σ w b i j = 0 := fun i => by
        rw [← hcoef i j]
        exact e1_eq_zero_of_notMem hj1 hj2 hjm1 hjm2 a i
      have k1 : b (j + 1) = 0 := by
        have hh := hz (-2)
        rw [e2_at_neg_two hn5] at hh
        exact sig_eq_zero hh
      have k3 : b (j - 1) = 0 := by
        have hh := hz 2
        rw [e2_at_two hn5] at hh
        exact sig_eq_zero ((mul_eq_zero.mp hh).resolve_left hwF)
      have k2 : b (j + 2) = 0 := by
        have hh := hz (-1)
        rw [e2_at_neg_one hn5, k3, map_zero, zero_add] at hh
        exact sig_eq_zero ((mul_eq_zero.mp hh).resolve_left hwF)
      have k4 : b (j - 2) = 0 := by
        have hh := hz 1
        rw [e2_at_one hn5, k1, map_zero, add_zero] at hh
        exact sig_eq_zero hh
      exact ⟨k1, k2, k3, k4⟩
    have he2zero : ∀ i : ZMod n, i ≠ 1 → e2 σ w b i (2 : ZMod n) = 0 := by
      intro i hi
      have hb3 : b (2 + 1 : ZMod n) = 0 := hbsupp _ (fun hh => z3 (by linear_combination hh))
      have hb1 : b (2 - 1 : ZMod n) = 0 := hbsupp _ (fun hh => z1 (by linear_combination hh))
      have hb4 : b (2 + 2 : ZMod n) = 0 := hbsupp _ (fun hh => z4 (by linear_combination hh))
      simp only [e2, if_neg hi, hb3, hb1, hb4, map_zero, add_zero, mul_zero, ite_self]
    have r1 : sig σ (1 : ZMod n) (a 0) = sig σ (2 : ZMod n) (b 0) := by
      have h := hcoef 1 2
      rw [e1_at_two hn5, show (1 : ZMod n) - 1 = 0 from by ring, e2_at_one hn5,
        show (2 : ZMod n) - 2 = 0 from by ring, show (2 : ZMod n) + 1 = 3 from by ring,
        hbsupp 3 z3, map_zero, add_zero] at h
      exact h
    have r2 : sig σ (-1 : ZMod n) (a 0) = sig σ (-2 : ZMod n) (b 0) := by
      have h := hcoef (-1) (-2)
      rw [e1_at_neg_two hn5, show (-1 : ZMod n) + 1 = 0 from by ring, e2_at_neg_one hn5,
        show (-2 : ZMod n) - 1 = -3 from by ring, show (-2 : ZMod n) + 2 = 0 from by ring,
        hbsupp (-3) (fun hh => z3 (by linear_combination -hh)), map_zero, zero_add] at h
      exact mul_left_cancel₀ hwF h
    have r3 : sig σ (1 : ZMod n) (a 0) = b 0 := by
      have h := congrArg (fun t => sig σ (2 : ZMod n) t) r2
      simp only at h
      rw [← sig_add_apply hsn, ← sig_add_apply hsn,
        show (2 : ZMod n) + -1 = 1 from by ring, show (2 : ZMod n) + -2 = 0 from by ring] at h
      simpa using h
    have hfixb : sig σ (2 : ZMod n) (b 0) = b 0 := by rw [← r1, r3]
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_unit_fixed hsgen hsn h2unit hfixb
    have ha0 : a 0 = algebraMap K F k := by
      have h := r3
      rw [← hk] at h
      have h2 := congrArg (fun t => (sig σ (1 : ZMod n)).symm t) h
      simpa using h2
    refine ⟨k, fun z => ?_⟩
    have hsum : ∑ i, a i * sig σ i z = a 0 * sig σ (0 : ZMod n) z :=
      Finset.sum_eq_single (0 : ZMod n)
        (fun i _ hi => by
          have h := hcoef (i + 1) 2
          rw [e1_at_two hn5, show i + 1 - 1 = i from by ring,
            he2zero (i + 1) (fun hh => hi (by linear_combination hh))] at h
          rw [sig_eq_zero h, zero_mul])
        (fun hcon => absurd (Finset.mem_univ _) hcon)
    rw [ha' z, lp, hsum, ha0]
    simp
  · rintro ⟨k, hk⟩ y
    exact ⟨algebraMap K F k * y, fun x => by rw [hk, famMul_smul_left, famMul_smul_right]⟩

omit hcop2 in
/-- **`thm:direct-nuclei`, second idealiser.**  The left idealiser of the spread set of the
family is the set of `K`-scalar multiplications. -/
theorem leftIdealiser_famC_eq (hcop3 : Nat.Coprime 3 n) :
    leftIdealiser (famC n σ w) = scalarMaps K F := by
  obtain ⟨z1, -, z3, z4⟩ := zmod_small_facts (n := n) hn5
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; norm_num at hw
  have hwF : algebraMap K F w ≠ 0 := fun h =>
    hw0 ((algebraMap K F).injective (by simpa using h))
  have h3unit : IsUnit (3 : ZMod n) := by
    have h33 : ((3 : ℕ) : ZMod n) = (3 : ZMod n) := by push_cast; ring
    rw [← h33, ZMod.isUnit_iff_coprime]; exact hcop3
  ext T
  simp only [scalarMaps, Set.mem_setOf_eq, mem_leftIdealiser_famC]
  constructor
  · intro hT
    choose B hB using hT
    have hTsmul : ∀ (k : K) (z : F), T (algebraMap K F k * z) = algebraMap K F k * T z := by
      intro k z
      obtain ⟨x, hx⟩ := famMul_left_surjective hP (y := 1) one_ne_zero z
      simp only at hx
      rw [← hx, ← famMul_smul_left, hB, hB, famMul_smul_left]
    let Tl : F →ₗ[K] F :=
      { toFun := T, map_add' := T.map_add,
        map_smul' := by
          intro k z
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hTsmul k z }
    have hBadd : ∀ y₁ y₂, B (y₁ + y₂) = B y₁ + B y₂ := by
      intro y₁ y₂
      refine famMul_right_cancel hP (fun x => ?_)
      rw [← hB, famMul_add_right, map_add, hB, hB, ← famMul_add_right]
    have hBsmul : ∀ (k : K) (y : F), B (algebraMap K F k * y) = algebraMap K F k * B y := by
      intro k y
      refine famMul_right_cancel hP (fun x => ?_)
      rw [← hB, famMul_smul_right, hTsmul, hB, famMul_smul_right]
    let Bl : F →ₗ[K] F :=
      { toFun := B, map_add' := hBadd,
        map_smul' := by
          intro k y
          simp only [RingHom.id_apply, Algebra.smul_def]
          exact hBsmul k y }
    obtain ⟨c, hc⟩ := exists_sig_expansion hsgen.injective hfin Tl
    obtain ⟨b, hb⟩ := exists_sig_expansion hsgen.injective hfin Bl
    have hc' : ∀ z, T z = lp σ c z := fun z => hc z
    have hb' : ∀ y, B y = lp σ b y := fun y => hb y
    have hcoef : ∀ i j, e3 w c i j = e2 σ w b i j := by
      have hzero : ∀ x y : F,
          ∑ i, ∑ j, (e3 w c i j - e2 σ w b i j) * (sig σ i x * sig σ j y) = 0 := by
        intro x y
        have hsplit : ∑ i, ∑ j, (e3 w c i j - e2 σ w b i j) * (sig σ i x * sig σ j y)
            = (∑ i, ∑ j, e3 w c i j * (sig σ i x * sig σ j y))
              - ∑ i, ∑ j, e2 σ w b i j * (sig σ i x * sig σ j y) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit, ← expand_e3 hsn c x y, ← expand_e2 hsn b x y, ← hc', ← hb', hB, sub_self]
      intro i j
      exact sub_eq_zero.mp (sig_bilinear_coeff_eq_zero hsgen.injective
        (fun i j => e3 w c i j - e2 σ w b i j) hzero i j)
    have hcsupp : ∀ m : ZMod n, m ≠ 0 → c m = 0 := by
      refine support_at_zero hn5 hcop c ?_
      rintro i ⟨hi1, hi2, him1, him2⟩
      have hz : ∀ j, e3 w c i j = 0 := fun j => by
        rw [hcoef i j]
        exact e2_eq_zero_of_notMem hi1 hi2 him1 him2 b j
      have k1 : c (i + 1) = 0 := by
        have hh := hz (i + 2)
        rw [e3_at_add_two (w := w) hn5 c i] at hh
        exact (mul_eq_zero.mp hh).resolve_left hwF
      have k3 : c (i - 1) = 0 := by
        have hh := hz (i - 2)
        rw [e3_at_sub_two (w := w) hn5 c i] at hh
        exact hh
      have k2 : c (i + 2) = 0 := by
        have hh := hz (i + 1)
        rw [e3_at_add_one (w := w) hn5 c i, k3, zero_add] at hh
        exact hh
      have k4 : c (i - 2) = 0 := by
        have hh := hz (i - 1)
        rw [e3_at_sub_one (w := w) hn5 c i, k1, add_zero] at hh
        exact (mul_eq_zero.mp hh).resolve_left hwF
      exact ⟨k1, k2, k3, k4⟩
    have key : ∀ j : ZMod n,
        sig σ (-1 : ZMod n) (b (j + 1)) = (if j = -1 then c 0 else 0) := by
      intro j
      have h := hcoef (-2) j
      rw [e2_at_neg_two hn5] at h
      rw [← h]
      have hm3 : c (-2 - 1 : ZMod n) = 0 := hcsupp _ (fun hh => z3 (by linear_combination -hh))
      have hm4 : c (-2 - 2 : ZMod n) = 0 := hcsupp _ (fun hh => z4 (by linear_combination -hh))
      have hm1 : c (-2 + 1 : ZMod n) = 0 := hcsupp _ (fun hh => z1 (by linear_combination -hh))
      simp only [e3, hm3, hm4, hm1, zero_add, add_zero, mul_zero, ite_self]
      rw [show (-2 : ZMod n) + 1 = -1 from by ring, show (-2 : ZMod n) + 2 = 0 from by ring]
    have hbsupp : ∀ m : ZMod n, m ≠ 0 → b m = 0 := by
      intro m hm
      have h := key (m - 1)
      rw [show m - 1 + 1 = m from by ring,
        if_neg (fun hh => hm (by linear_combination hh))] at h
      exact sig_eq_zero h
    have hb0 : sig σ (-1 : ZMod n) (b 0) = c 0 := by
      have h := key (-1)
      rw [show (-1 : ZMod n) + 1 = 0 from by ring, if_pos rfl] at h
      exact h
    have hc0 : c 0 = sig σ (2 : ZMod n) (b 0) := by
      have h := hcoef 1 2
      have E := e3_at_add_one (w := w) hn5 c 1
      rw [show (1 : ZMod n) + 1 = 2 from by ring, show (1 : ZMod n) - 1 = 0 from by ring,
        show (1 : ZMod n) + 2 = 3 from by ring] at E
      rw [E, hcsupp 3 z3, add_zero, e2_at_one hn5, show (2 : ZMod n) - 2 = 0 from by ring,
        show (2 : ZMod n) + 1 = 3 from by ring, hbsupp 3 z3, map_zero, add_zero] at h
      exact h
    have hfixb : sig σ (3 : ZMod n) (b 0) = b 0 := by
      have h := hb0.trans hc0
      have h2 := congrArg (fun t => sig σ (1 : ZMod n) t) h
      simp only at h2
      rw [← sig_add_apply hsn, ← sig_add_apply hsn,
        show (1 : ZMod n) + -1 = 0 from by ring, show (1 : ZMod n) + 2 = 3 from by ring] at h2
      simpa using h2.symm
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_unit_fixed hsgen hsn h3unit hfixb
    have hc0k : c 0 = algebraMap K F k := by
      rw [← hb0, ← hk, sig_algebraMap]
    refine ⟨k, fun z => ?_⟩
    have hsum : ∑ i, c i * sig σ i z = c 0 * sig σ (0 : ZMod n) z :=
      Finset.sum_eq_single (0 : ZMod n) (fun i _ hi => by rw [hcsupp i hi, zero_mul])
        (fun hcon => absurd (Finset.mem_univ _) hcon)
    rw [hc' z, lp, hsum, hc0k]
    simp
  · rintro ⟨k, hk⟩ y
    exact ⟨algebraMap K F k * y, fun x => by rw [hk, famMul_smul_right]⟩

end Main

end Semifields
