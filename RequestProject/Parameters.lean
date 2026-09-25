import RequestProject.Dickson
import RequestProject.Idealisers

/-!
# Generator parameters (`thm:parameters`, `K`-linear case, prime dimension)

For a prime `n ≥ 5` we show that two members of the family built from the same parameter `w`
but from two generators `τ₁, τ₂` of the Galois group are `K`-linearly isotopic only when
`τ₁ = τ₂`.  This is the part of `thm:parameters` / `cor:parametercount` needed for the count
of isotopy classes in `cor:menichetti`.

The proof follows the paper: the monomial lemma (`lem:monomial`), applied to the left pencil
and, after cyclic rotation (`eq:cyclic-tensor`), to the other two components, shows that the
three maps are linearized monomials `x ↦ a τ₁^i(x)`.  A comparison of the six-term supports
then forces `τ₂ = τ₁^{±1}`, and the coefficients exclude `τ₂ = τ₁⁻¹`.
-/

namespace Semifields

open scoped BigOperators
open Matrix

section Support

variable {n : ℕ}

/-- First exponents of the six terms of the multiplication `eq:construction`. -/
def alZ : Fin 6 → ℤ := ![1, 1, -2, 2, -1, -1]

/-- Second exponents of the six terms of the multiplication `eq:construction`. -/
def beZ : Fin 6 → ℤ := ![2, -1, -1, 1, 1, -2]

/-- The support point of the `t`-th term after the substitution `x ↦ τ^i(x)`, `y ↦ τ^j(y)`
and the change of generator `τ ↦ τ^u`. -/
def suppPt (u i j : ZMod n) (t : Fin 6) : ZMod n × ZMod n :=
  (u * (alZ t : ZMod n) + i, u * (beZ t : ZMod n) + j)

lemma abs_alZ_le (t : Fin 6) : |alZ t| ≤ 2 := by fin_cases t <;> decide
lemma abs_beZ_le (t : Fin 6) : |beZ t| ≤ 2 := by fin_cases t <;> decide

lemma alZ_beZ_inj : ∀ t t' : Fin 6, alZ t = alZ t' → beZ t = beZ t' → t = t' := by decide

lemma intCast_inj_small (hn5 : 5 ≤ n) {a b : ℤ} (ha : |a| ≤ 2) (hb : |b| ≤ 2)
    (h : (a : ZMod n) = b) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have h0 : b - a = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    have : |b - a| ≤ 4 := by
      calc |b - a| ≤ |b| + |a| := abs_sub _ _
        _ ≤ 4 := by linarith
    omega
  linarith

lemma suppPt_injective (hn : n.Prime) (hn5 : 5 ≤ n) {u : ZMod n} (hu : u ≠ 0) (i j : ZMod n) :
    Function.Injective (suppPt u i j) := by
  haveI := Fact.mk hn
  intro t t' h
  simp only [suppPt, Prod.mk.injEq, add_left_inj] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := mul_left_cancel₀ hu h1
  have h2' := mul_left_cancel₀ hu h2
  exact alZ_beZ_inj t t' (intCast_inj_small hn5 (abs_alZ_le t) (abs_alZ_le t') h1')
    (intCast_inj_small hn5 (abs_beZ_le t) (abs_beZ_le t') h2')

lemma sum_suppPt_fst (u i j : ZMod n) : ∑ t, (suppPt u i j t).1 = 6 * i := by
  simp [Fin.sum_univ_six, suppPt, alZ]; ring

lemma sum_suppPt_snd (u i j : ZMod n) : ∑ t, (suppPt u i j t).2 = 6 * j := by
  simp [Fin.sum_univ_six, suppPt, beZ]; ring

lemma sum_sq_suppPt_fst (u i j : ZMod n) : ∑ t, ((suppPt u i j t).1 - i) ^ 2 = 12 * u ^ 2 := by
  simp [Fin.sum_univ_six, suppPt, alZ]; ring

/-- Small integers are nonzero modulo a prime `n ≥ 5`. -/
lemma natCast_ne_zero_of_lt (hn5 : 5 ≤ n) (hn : n.Prime) {m : ℕ}
    (hmn : ∀ q, q.Prime → q ∣ m → q < 5) : (m : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have := hmn n hn hd
  omega

end Support

section Coefficients

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {τ : F ≃ₐ[K] F}

/-- **Comparison of coefficients** of two bilinearized expressions. -/
theorem coeff_match {T : Type*} [Fintype T]
    (hinj : Function.Injective (fun i : ZMod n => sig τ i))
    (pL pR : T → ZMod n × ZMod n) (vL vR : T → F)
    (h : ∀ x y : F, ∑ t, vL t * (sig τ (pL t).1 x * sig τ (pL t).2 y)
      = ∑ t, vR t * (sig τ (pR t).1 x * sig τ (pR t).2 y)) (m : ZMod n × ZMod n) :
    ∑ t ∈ Finset.univ.filter (fun t => pL t = m), vL t
      = ∑ t ∈ Finset.univ.filter (fun t => pR t = m), vR t := by
  classical
  have hfib : ∀ (p : T → ZMod n × ZMod n) (v : T → F) (x y : F),
      ∑ m : ZMod n × ZMod n, (∑ t ∈ Finset.univ.filter (fun t => p t = m), v t)
          * (sig τ m.1 x * sig τ m.2 y)
        = ∑ t, v t * (sig τ (p t).1 x * sig τ (p t).2 y) := by
    intro p v x y
    simp only [Finset.sum_mul]
    rw [← Finset.sum_fiberwise Finset.univ p (fun t => v t * (sig τ (p t).1 x * sig τ (p t).2 y))]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun t ht => ?_))
    rw [(Finset.mem_filter.mp ht).2]
  have hc := sig_bilinear_coeff_eq_zero hinj
    (fun a b => (∑ t ∈ Finset.univ.filter (fun t => pL t = (a, b)), vL t)
      - ∑ t ∈ Finset.univ.filter (fun t => pR t = (a, b)), vR t) (fun x y => by
        have e := (hfib pL vL x y).trans ((h x y).trans (hfib pR vR x y).symm)
        rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Fintype.sum_prod_type] at e
        rw [← e]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        ring)
  exact sub_eq_zero.mp (hc m.1 m.2)

omit [NeZero n] in
lemma sum_filter_eq_single {T : Type*} [Fintype T] {p : T → ZMod n × ZMod n}
    (hp : Function.Injective p) (v : T → F) (s : T) :
    ∑ t ∈ Finset.univ.filter (fun t => p t = p s), v t = v s := by
  classical
  rw [Finset.sum_eq_single s]
  · intro t ht hts
    exact absurd (hp (Finset.mem_filter.mp ht).2) hts
  · intro hs
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, rfl⟩ :
      s ∈ Finset.univ.filter (fun t => p t = p s)) hs

end Coefficients

section Key

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {τ : F ≃ₐ[K] F}

/-- Coefficients of the six terms of the multiplication `eq:construction`. -/
def gam (w : K) : Fin 6 → K := ![1, 1, 1, w, w, w]

/-- Index of the term with negated exponents. -/
def negIdx : Fin 6 → Fin 6 := ![5, 4, 3, 2, 1, 0]

lemma negIdx_spec : ∀ s t : Fin 6, alZ t = -alZ s → beZ t = -beZ s → t = negIdx s := by decide

omit [NeZero n] in
lemma famMul_eq_sum [NeZero n] (w : K) (x y : F) :
    famMul n τ w x y = ∑ t, algebraMap K F (gam w t)
      * (sig τ (alZ t : ZMod n) x * sig τ (beZ t : ZMod n) y) := by
  simp [famMul, Fin.sum_univ_six, gam, alZ, beZ]
  ring

omit [NeZero n] in
/-- Powers of a power of `τ`. -/
lemma sig_sig (hτ : τ ^ n = 1) (u m : ZMod n) : sig (sig τ u) m = sig τ (u * m) := by
  simp only [sig]
  rw [← pow_mul, ZMod.val_mul, pow_mod_of_pow_eq_one hτ]

lemma lhs_expand (hτ : τ ^ n = 1) (w : K) (u i j : ZMod n) (a b x y : F) :
    famMul n (sig τ u) w (a * sig τ i x) (b * sig τ j y)
      = ∑ t, (algebraMap K F (gam w t) * sig τ (u * (alZ t : ZMod n)) a
          * sig τ (u * (beZ t : ZMod n)) b)
        * (sig τ (suppPt u i j t).1 x * sig τ (suppPt u i j t).2 y) := by
  rw [famMul_eq_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [sig_sig hτ, map_mul, suppPt, sig_add_apply hτ]
  ring

lemma rhs_expand (hτ : τ ^ n = 1) (w : K) (k : ZMod n) (c x y : F) :
    c * sig τ k (famMul n τ w x y)
      = ∑ t, (c * algebraMap K F (gam w t))
        * (sig τ (suppPt 1 k k t).1 x * sig τ (suppPt 1 k k t).2 y) := by
  rw [famMul_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [map_mul, sig_algebraMap, suppPt, one_mul]
  rw [add_comm (alZ t : ZMod n) k, add_comm (beZ t : ZMod n) k, sig_add_apply hτ,
    sig_add_apply hτ]
  ring

/-- **The support comparison of `thm:parameters`.**  If a member of the family written with
the generator `τ^u` is carried to the member written with `τ` by linearized monomials, then
`u = 1`. -/
theorem eq_one_of_monomial_isotopy (hn : n.Prime) (hn5 : 5 ≤ n)
    (hinj : Function.Injective (fun i : ZMod n => sig τ i)) (hτ : τ ^ n = 1) {w : K}
    (hw : w ^ 2 - w + 1 = 0) (h3 : (3 : K) ≠ 0) {u i j k : ZMod n} (hu : u ≠ 0) {a b c : F}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ x y, famMul n (sig τ u) w (a * sig τ i x) (b * sig τ j y)
      = c * sig τ k (famMul n τ w x y)) : u = 1 := by
  classical
  haveI := Fact.mk hn
  set vL : Fin 6 → F := fun t => algebraMap K F (gam w t) * sig τ (u * (alZ t : ZMod n)) a
    * sig τ (u * (beZ t : ZMod n)) b with hvLdef
  set vR : Fin 6 → F := fun t => c * algebraMap K F (gam w t) with hvRdef
  have hcoef := coeff_match hinj (suppPt u i j) (suppPt 1 k k) vL vR (fun x y => by
    rw [← lhs_expand hτ, ← rhs_expand hτ, h])
  have hLinj := suppPt_injective hn hn5 hu i j
  have hRinj := suppPt_injective hn hn5 (one_ne_zero : (1 : ZMod n) ≠ 0) k k
  have hw0 : w ≠ 0 := by
    rintro rfl; norm_num at hw
  have hgam : ∀ t, gam w t ≠ 0 := by
    intro t; fin_cases t <;> simp [gam, hw0]
  have hvL : ∀ t, vL t ≠ 0 := fun t => mul_ne_zero (mul_ne_zero
    (by simpa using hgam t) (sig_ne_zero ha)) (sig_ne_zero hb)
  have hex : ∀ s, ∃ t, suppPt 1 k k t = suppPt u i j s := by
    intro s
    by_contra hne
    push_neg at hne
    have := hcoef (suppPt u i j s)
    rw [sum_filter_eq_single hLinj, Finset.sum_eq_zero
      (fun t ht => absurd (Finset.mem_filter.mp ht).2 (hne t))] at this
    exact hvL s this
  choose f hf using hex
  have hfinj : Function.Injective f := fun s s' hss' =>
    hLinj (by rw [← hf s, ← hf s', hss'])
  have hfbij : Function.Bijective f := ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  set e := Equiv.ofBijective f hfbij
  have hsumf : ∀ g : ZMod n × ZMod n → ZMod n,
      ∑ s, g (suppPt u i j s) = ∑ t, g (suppPt 1 k k t) := by
    intro g
    rw [← e.sum_comp (fun t => g (suppPt 1 k k t))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [e, Equiv.ofBijective_apply, hf s]
  have hnd2 : ¬ n ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hnd3 : ¬ n ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h6 : (6 : ZMod n) ≠ 0 := by
    have : ((6 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, show (6 : ℕ) = 2 * 3 by norm_num]
      intro h
      rcases (Nat.Prime.dvd_mul hn).mp h with h | h
      · exact hnd2 h
      · exact hnd3 h
    simpa using this
  have h12 : (12 : ZMod n) ≠ 0 := by
    have : ((12 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, show (12 : ℕ) = 2 * (2 * 3) by norm_num]
      intro h
      rcases (Nat.Prime.dvd_mul hn).mp h with h | h
      · exact hnd2 h
      rcases (Nat.Prime.dvd_mul hn).mp h with h | h
      · exact hnd2 h
      · exact hnd3 h
    simpa using this
  have hik : i = k := by
    have := hsumf Prod.fst
    rw [sum_suppPt_fst, sum_suppPt_fst] at this
    exact mul_left_cancel₀ h6 this
  have hjk : j = k := by
    have := hsumf Prod.snd
    rw [sum_suppPt_snd, sum_suppPt_snd] at this
    exact mul_left_cancel₀ h6 this
  subst hik hjk
  have hu2 : u * u = 1 := by
    have := hsumf (fun m => (m.1 - j) ^ 2)
    simp only at this
    rw [sum_sq_suppPt_fst, sum_sq_suppPt_fst] at this
    have := mul_left_cancel₀ h12 this
    rw [one_pow] at this
    rw [← this]; ring
  rcases mul_self_eq_one_iff.mp hu2 with hu1 | hu1
  · exact hu1
  exfalso
  subst hu1
  -- identify the matching terms
  have hfneg : ∀ s, f s = negIdx s := by
    intro s
    have hfs := hf s
    simp only [suppPt, Prod.mk.injEq, add_left_inj, one_mul] at hfs
    refine negIdx_spec s (f s) ?_ ?_
    · refine intCast_inj_small hn5 (abs_alZ_le _) (by rw [abs_neg]; exact abs_alZ_le s) ?_
      rw [hfs.1]; push_cast; ring
    · refine intCast_inj_small hn5 (abs_beZ_le _) (by rw [abs_neg]; exact abs_beZ_le s) ?_
      rw [hfs.2]; push_cast; ring
  have hval : ∀ s, vL s = vR (negIdx s) := by
    intro s
    have := hcoef (suppPt (-1) j j s)
    rw [sum_filter_eq_single hLinj, ← hf s, sum_filter_eq_single hRinj, hfneg s] at this
    exact this
  have e0 := hval 0
  have e3 := hval 3
  have e4 := hval 4
  have e5 := hval 5
  simp only [hvLdef, hvRdef, gam, alZ, beZ, negIdx] at e0 e3 e4 e5
  simp at e0 e3 e4 e5
  set W := algebraMap K F w with hWdef
  have hW0 : W ≠ 0 := fun h0 => hw0 ((algebraMap K F).injective (by rw [← hWdef, h0, map_zero]))
  have hsig : ∀ (p q : ZMod n) (z : F), sig τ p (sig τ q z) = sig τ (p + q) z :=
    fun p q z => (sig_add_apply hτ p q z).symm
  have hb1 : sig τ (-1 : ZMod n) b = sig τ (2 : ZMod n) b :=
    mul_left_cancel₀ (mul_ne_zero hW0 (sig_ne_zero ha)) (e4.trans e5.symm)
  have hb3 : sig τ (3 : ZMod n) b = b := by
    have := congrArg (sig τ (1 : ZMod n)) hb1
    rw [hsig, hsig, show (1 : ZMod n) + -1 = 0 by ring, show (1 : ZMod n) + 2 = 3 by ring,
      sig_zero] at this
    exact this.symm
  have ha1 : sig τ (-2 : ZMod n) a = sig τ (1 : ZMod n) a := by
    have h1 := mul_right_cancel₀ (sig_ne_zero hb) (e3.trans e4.symm)
    exact mul_left_cancel₀ hW0 h1
  have ha3 : sig τ (3 : ZMod n) a = a := by
    have := congrArg (sig τ (2 : ZMod n)) ha1
    rw [hsig, hsig, show (2 : ZMod n) + -2 = 0 by ring, show (2 : ZMod n) + 1 = 3 by ring,
      sig_zero] at this
    exact this.symm
  have h3n : (3 : ZMod n) ≠ 0 := by
    have : ((3 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd3
    simpa using this
  have hfix : ∀ z : F, sig τ (3 : ZMod n) z = z → ∀ m : ZMod n, sig τ m z = z := by
    intro z hz m
    have := sig_fixed_mul hτ hz (3⁻¹ * m)
    rwa [← mul_assoc, mul_inv_cancel₀ h3n, one_mul] at this
  rw [hfix a ha3, hfix b hb3] at e0
  rw [hfix a ha3, hfix b hb3] at e4
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hW2 : W ^ 2 = 1 := by
    have h1 : a * b * (W ^ 2 - 1) = 0 := by
      linear_combination W * e4 - e0
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hab
    · linear_combination h
  have hwF : W ^ 2 - W + 1 = 0 := by
    have := congrArg (algebraMap K F) hw
    simpa [hWdef] using this
  have h3F : (3 : F) = 0 := by linear_combination (-1 - W) * hW2 + (W + 2) * hwF
  exact h3 ((algebraMap K F).injective (by rw [map_ofNat, map_zero]; exact h3F))

end Key

section Classification

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
variable {n : ℕ} [NeZero n]

omit [FiniteDimensional K F] [IsGalois K F] in
lemma pow_eq_one_of_bij {τ : F ≃ₐ[K] F} [Fintype (F ≃ₐ[K] F)]
    (h : Function.Bijective (fun i : ZMod n => sig τ i)) : τ ^ n = 1 := by
  have hcard : Fintype.card (F ≃ₐ[K] F) = n := by
    rw [← Fintype.card_of_bijective h, ZMod.card]
  rw [← hcard]
  exact pow_card_eq_one

lemma finrank_of_bij {τ : F ≃ₐ[K] F} (h : Function.Bijective (fun i : ZMod n => sig τ i)) :
    Module.finrank K F = n := by
  rw [← IsGalois.card_aut_eq_finrank K F, Nat.card_eq_fintype_card,
    ← Fintype.card_of_bijective h, ZMod.card]

/-- **Lemma `lem:monomial` for the family.**  Every `K`-linear isotopism between two members
of the family (written with two generators `τ₁, τ₂`) consists of linearized monomials. -/
theorem famMul_isotopism_monomial (hn5 : 5 ≤ n) (hmod : n % 6 = 1 ∨ n % 6 = 5)
    {τ₁ τ₂ : F ≃ₐ[K] F} (h₁ : Function.Bijective (fun i : ZMod n => sig τ₁ i))
    (h₂ : Function.Bijective (fun i : ZMod n => sig τ₂ i)) {w : K} (hw : w ^ 2 - w + 1 = 0)
    (h3 : (3 : K) ≠ 0) {A B C : F ≃ₗ[K] F}
    (hABC : ∀ x y, famMul n τ₂ w (A x) (B y) = C (famMul n τ₁ w x y)) :
    (∃ a : F, a ≠ 0 ∧ ∃ i : ZMod n, ∀ x, A x = a * sig τ₁ i x) ∧
      (∃ b : F, b ≠ 0 ∧ ∃ j : ZMod n, ∀ y, B y = b * sig τ₁ j y) ∧
      (∃ c : F, c ≠ 0 ∧ ∃ k : ZMod n, ∀ z, C z = c * sig τ₁ k z) := by
  have hodd : Odd n := by rcases hmod with h | h <;> exact ⟨n / 2, by omega⟩
  have hτ₁ := pow_eq_one_of_bij h₁
  have hτ₂ := pow_eq_one_of_bij h₂
  have hfin := finrank_of_bij h₁
  obtain ⟨DA, hDA⟩ := exists_dickson h₁.1 hfin τ₂ A.toLinearMap
  obtain ⟨DB, hDB⟩ := exists_dickson h₁.1 hfin τ₂ B.toLinearMap
  obtain ⟨DC, hDC⟩ := exists_dickson h₁.1 hfin τ₂ C.toLinearMap
  have uA := isUnit_det_of_isDickson h₁.1 h₂.1 hfin (T := A) hDA
  have uB := isUnit_det_of_isDickson h₁.1 h₂.1 hfin (T := B) hDB
  have uC := isUnit_det_of_isDickson h₁.1 h₂.1 hfin (T := C) hDC
  have hiso := pencilIso_famMul hτ₁ hτ₂ h₁.1 hABC hDA hDB hDC
  set w' := algebraMap K F w with hw'def
  have hw' : w' ^ 2 - w' + 1 = 0 := by
    have := congrArg (algebraMap K F) hw
    simpa [hw'def] using this
  set lamF : F := (1 + w' ^ n) ^ 2 * (1 - w' ^ (2 * n)) with hlamF
  have hlam0 : lamF ≠ 0 := by
    have hl := lam_ne_zero hw h3 hmod
    have : lamF = algebraMap K F (lam w n) := by simp [hlamF, lam, hw'def]
    rw [this]
    exact fun h0 => hl ((algebraMap K F).injective (by rw [h0, map_zero]))
  have hQ := det_pen_lwP w' hw' hodd (by omega)
  have hcyc := pencilCyclic_lwP (n := n) w'
  have mA : RowMonomial DA :=
    rowMonomial_of_pencilIso hiso lamF lamF hQ (hQ _) hlam0 uC.ne_zero
  have uAT : IsUnit (DAᵀ)⁻¹.det := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det DA uA
  have uCT : IsUnit (DCᵀ)⁻¹.det := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det DC uC
  have uBT : IsUnit (DBᵀ)⁻¹.det := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det DB uB
  have rot1 := pencilIso_rotate hcyc hiso uA uC
  have mB : RowMonomial DB :=
    rowMonomial_of_pencilIso rot1 lamF lamF hQ (hQ _) hlam0 uAT.ne_zero
  have rot2 := pencilIso_rotate hcyc rot1 uB uAT
  have mCT : RowMonomial (DCᵀ)⁻¹ :=
    rowMonomial_of_pencilIso rot2 lamF lamF hQ (hQ _) hlam0 uBT.ne_zero
  have mC' := rowMonomial_inv_transpose mCT uCT.ne_zero
  have hCeq : (((DCᵀ)⁻¹)ᵀ)⁻¹ = DC := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
      (by rwa [Matrix.det_transpose]), Matrix.transpose_transpose]
  rw [hCeq] at mC'
  exact ⟨monomial_of_isDickson hDA mA, monomial_of_isDickson hDB mB,
    monomial_of_isDickson hDC mC'⟩

/-- **`thm:parameters`, `K`-linear case, in prime dimension.**  For a prime `n ≥ 5`, two
members of the family with the same parameter `w`, written with generators `τ₁` and `τ₂` of
the Galois group, are `K`-linearly isotopic only if `τ₁ = τ₂`. -/
theorem eq_of_isotopicLin_famMul (hn : n.Prime) (hn5 : 5 ≤ n) {τ₁ τ₂ : F ≃ₐ[K] F}
    (h₁ : Function.Bijective (fun i : ZMod n => sig τ₁ i))
    (h₂ : Function.Bijective (fun i : ZMod n => sig τ₂ i)) {w : K} (hw : w ^ 2 - w + 1 = 0)
    (h3 : (3 : K) ≠ 0) (hiso : IsotopicLin K (famMul n τ₁ w) (famMul n τ₂ w)) : τ₁ = τ₂ := by
  obtain ⟨A, B, C, hABC⟩ := hiso
  have hmod : n % 6 = 1 ∨ n % 6 = 5 := by
    have h2 : ¬ 2 ∣ n := fun h => by
      rcases (Nat.dvd_prime hn).mp h with h | h <;> omega
    have h3' : ¬ 3 ∣ n := fun h => by
      rcases (Nat.dvd_prime hn).mp h with h | h <;> omega
    omega
  obtain ⟨⟨a, ha, i, hA⟩, ⟨b, hb, j, hB⟩, ⟨c, -, k, hC⟩⟩ :=
    famMul_isotopism_monomial hn5 hmod h₁ h₂ hw h3 hABC
  have hτ₁ := pow_eq_one_of_bij h₁
  obtain ⟨u, hu⟩ := h₁.2 τ₂
  simp only at hu
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h01 : sig τ₂ (0 : ZMod n) = sig τ₂ (1 : ZMod n) := by
      simp only [sig_zero]
      rw [← hu]
      simp [sig, ZMod.val_one]
    exact zero_ne_one (h₂.1 h01)
  have key : ∀ x y, famMul n (sig τ₁ u) w (a * sig τ₁ i x) (b * sig τ₁ j y)
      = c * sig τ₁ k (famMul n τ₁ w x y) := by
    intro x y
    rw [hu, ← hA, ← hB, ← hC]
    exact hABC x y
  have hu1 := eq_one_of_monomial_isotopy hn hn5 h₁.1 hτ₁ hw h3 hu0 ha hb key
  rw [← hu, hu1]
  simp [sig, ZMod.val_one]

end Classification

end Semifields
