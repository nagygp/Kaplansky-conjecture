import RequestProject.Linearized

/-!
# The nuclei of the new family (`thm:direct-nuclei`)

This file computes the idealisers of the spread set and of the dual spread set of the
family `𝒫_{w,s}`.  The computation follows the proof of `thm:direct-nuclei`: an idealiser
element gives an identity of `K`-bilinear maps, which is expanded in the basis
`(x, y) ↦ σ^i x · σ^j y` and compared coefficientwise.
-/

namespace Semifields

open scoped BigOperators

section Expansions

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

/-- A linearized polynomial in `σ`. -/
def lp (σ : F ≃ₐ[K] F) (c : ZMod n → F) (x : F) : F := ∑ i, c i * sig σ i x

lemma sum_pt (t : ZMod n) (z : F) (y : F) :
    ∑ j, (if j = t then z else 0) * sig σ j y = z * sig σ t y := by
  rw [Finset.sum_eq_single t]
  · simp
  · intro k _ hk; simp [hk]
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- Applying a power of `σ` to a linearized polynomial, after reindexing. -/
lemma sig_lp (hσ : σ ^ n = 1) (k : ZMod n) (c : ZMod n → F) (x : F) :
    sig σ k (lp σ c x) = ∑ i, sig σ k (c (i - k)) * sig σ i x := by
  rw [lp, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ (fun m => ?_)
  have h1 : (Equiv.addRight k) m - k = m := by simp
  have h2 : (Equiv.addRight k) m = k + m := by simp [add_comm]
  rw [h1, h2, map_mul, sig_add_apply hσ]


/-- Applying a power of `σ` to a product of the family. -/
lemma sig_famMul (hσ : σ ^ n = 1) (k : ZMod n) (x y : F) :
    sig σ k (famMul n σ w x y)
      = sig σ (k + 1) x * sig σ (k + 2) y + sig σ (k + 1) x * sig σ (k - 1) y
        + sig σ (k - 2) x * sig σ (k - 1) y
        + algebraMap K F w * (sig σ (k + 2) x * sig σ (k + 1) y
            + sig σ (k - 1) x * sig σ (k + 1) y + sig σ (k - 1) x * sig σ (k - 2) y) := by
  simp only [famMul, map_add, map_mul, sig_algebraMap, ← sig_add_apply hσ]
  rw [show k + -1 = k - 1 from by ring, show k + -2 = k - 2 from by ring]

lemma sum_reindex (d : ZMod n) (f : ZMod n → F) : ∑ i : ZMod n, f (i - d) = ∑ k, f k :=
  Fintype.sum_equiv (Equiv.subRight d) (fun i => f (i - d)) f (fun _ => rfl)

/-- Coefficients of `(A x) * y` in the basis `σ^i x · σ^j y`, for `A` a linearized
polynomial with coefficients `a`. -/
def e1 (σ : F ≃ₐ[K] F) (w : K) (a : ZMod n → F) (i j : ZMod n) : F :=
  (if j = 2 then sig σ (1 : ZMod n) (a (i - 1)) else 0)
    + (if j = -1 then sig σ (1 : ZMod n) (a (i - 1)) + sig σ (-2 : ZMod n) (a (i + 2)) else 0)
    + (if j = 1 then algebraMap K F w *
        (sig σ (2 : ZMod n) (a (i - 2)) + sig σ (-1 : ZMod n) (a (i + 1))) else 0)
    + (if j = -2 then algebraMap K F w * sig σ (-1 : ZMod n) (a (i + 1)) else 0)

/-- Coefficients of `x * (B y)`. -/
def e2 (σ : F ≃ₐ[K] F) (w : K) (b : ZMod n → F) (i j : ZMod n) : F :=
  (if i = 1 then sig σ (2 : ZMod n) (b (j - 2)) + sig σ (-1 : ZMod n) (b (j + 1)) else 0)
    + (if i = -2 then sig σ (-1 : ZMod n) (b (j + 1)) else 0)
    + (if i = 2 then algebraMap K F w * sig σ (1 : ZMod n) (b (j - 1)) else 0)
    + (if i = -1 then algebraMap K F w *
        (sig σ (1 : ZMod n) (b (j - 1)) + sig σ (-2 : ZMod n) (b (j + 2))) else 0)

/-- Coefficients of `T (x * y)`, for `T` a linearized polynomial with coefficients `c`. -/
def e3 (w : K) (c : ZMod n → F) (i j : ZMod n) : F :=
  (if j = i + 1 then c (i - 1) + c (i + 2) else 0)
    + (if j = i - 2 then c (i - 1) else 0)
    + (if j = i - 1 then algebraMap K F w * (c (i - 2) + c (i + 1)) else 0)
    + (if j = i + 2 then algebraMap K F w * c (i + 1) else 0)

lemma expand_e1 (hσ : σ ^ n = 1) (a : ZMod n → F) (x y : F) :
    famMul n σ w (lp σ a x) y = ∑ i : ZMod n, ∑ j : ZMod n,
      e1 σ w a i j * (sig σ i x * sig σ j y) := by
  have hleft : famMul n σ w (lp σ a x) y
      = ∑ i : ZMod n,
        (sig σ (1 : ZMod n) (a (i - 1)) * (sig σ i x * sig σ (2 : ZMod n) y)
          + (sig σ (1 : ZMod n) (a (i - 1)) + sig σ (-2 : ZMod n) (a (i + 2)))
              * (sig σ i x * sig σ (-1 : ZMod n) y)
          + algebraMap K F w * (sig σ (2 : ZMod n) (a (i - 2)) + sig σ (-1 : ZMod n) (a (i + 1)))
              * (sig σ i x * sig σ (1 : ZMod n) y)
          + algebraMap K F w * sig σ (-1 : ZMod n) (a (i + 1))
              * (sig σ i x * sig σ (-2 : ZMod n) y)) := by
    rw [famMul]
    simp only [sig_lp hσ, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring_nf)
  rw [hleft]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : ∑ j : ZMod n, e1 σ w a i j * (sig σ i x * sig σ j y)
      = sig σ i x * ∑ j : ZMod n, e1 σ w a i j * sig σ j y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this]
  simp only [e1, add_mul, Finset.sum_add_distrib, sum_pt]
  ring

lemma expand_e2 (hσ : σ ^ n = 1) (b : ZMod n → F) (x y : F) :
    famMul n σ w x (lp σ b y) = ∑ i : ZMod n, ∑ j : ZMod n,
      e2 σ w b i j * (sig σ i x * sig σ j y) := by
  have hright : famMul n σ w x (lp σ b y)
      = ∑ j : ZMod n,
        ((sig σ (2 : ZMod n) (b (j - 2)) + sig σ (-1 : ZMod n) (b (j + 1)))
            * (sig σ (1 : ZMod n) x * sig σ j y)
          + sig σ (-1 : ZMod n) (b (j + 1)) * (sig σ (-2 : ZMod n) x * sig σ j y)
          + algebraMap K F w * sig σ (1 : ZMod n) (b (j - 1))
              * (sig σ (2 : ZMod n) x * sig σ j y)
          + algebraMap K F w * (sig σ (1 : ZMod n) (b (j - 1))
              + sig σ (-2 : ZMod n) (b (j + 2))) * (sig σ (-1 : ZMod n) x * sig σ j y)) := by
    rw [famMul]
    simp only [sig_lp hσ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring_nf)
  rw [hright, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : ∑ i : ZMod n, e2 σ w b i j * (sig σ i x * sig σ j y)
      = (∑ i : ZMod n, e2 σ w b i j * sig σ i x) * sig σ j y := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]
  simp only [e2, add_mul, Finset.sum_add_distrib, sum_pt]
  ring

lemma expand_e3 (hσ : σ ^ n = 1) (c : ZMod n → F) (x y : F) :
    lp σ c (famMul n σ w x y) = ∑ i : ZMod n, ∑ j : ZMod n,
      e3 w c i j * (sig σ i x * sig σ j y) := by
  have hrhs : ∀ i : ZMod n, ∑ j : ZMod n, e3 w c i j * (sig σ i x * sig σ j y)
      = (c (i - 1) + c (i + 2)) * (sig σ i x * sig σ (i + 1) y)
        + c (i - 1) * (sig σ i x * sig σ (i - 2) y)
        + algebraMap K F w * (c (i - 2) + c (i + 1)) * (sig σ i x * sig σ (i - 1) y)
        + algebraMap K F w * c (i + 1) * (sig σ i x * sig σ (i + 2) y) := by
    intro i
    have hpull : ∑ j : ZMod n, e3 w c i j * (sig σ i x * sig σ j y)
        = sig σ i x * ∑ j : ZMod n, e3 w c i j * sig σ j y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hpull]
    simp only [e3, add_mul, Finset.sum_add_distrib, sum_pt]
    ring
  rw [lp]
  have hterm : ∀ k : ZMod n, c k * sig σ k (famMul n σ w x y)
      = c k * (sig σ (k + 1) x * sig σ (k + 2) y) + c k * (sig σ (k + 1) x * sig σ (k - 1) y)
        + c k * (sig σ (k - 2) x * sig σ (k - 1) y)
        + (algebraMap K F w * c k) * (sig σ (k + 2) x * sig σ (k + 1) y)
        + (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k + 1) y)
        + (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k - 2) y) := by
    intro k
    rw [sig_famMul hσ]
    ring
  have r1 : ∑ k : ZMod n, c k * (sig σ (k + 1) x * sig σ (k + 2) y)
      = ∑ i : ZMod n, c (i - 1) * (sig σ i x * sig σ (i + 1) y) := by
    rw [← sum_reindex 1 (fun k => c k * (sig σ (k + 1) x * sig σ (k + 2) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - 1 + 1 = i from by ring, show i - 1 + 2 = i + 1 from by ring])
  have r2 : ∑ k : ZMod n, c k * (sig σ (k + 1) x * sig σ (k - 1) y)
      = ∑ i : ZMod n, c (i - 1) * (sig σ i x * sig σ (i - 2) y) := by
    rw [← sum_reindex 1 (fun k => c k * (sig σ (k + 1) x * sig σ (k - 1) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - 1 + 1 = i from by ring, show i - 1 - 1 = i - 2 from by ring])
  have r3 : ∑ k : ZMod n, c k * (sig σ (k - 2) x * sig σ (k - 1) y)
      = ∑ i : ZMod n, c (i + 2) * (sig σ i x * sig σ (i + 1) y) := by
    rw [← sum_reindex (-2) (fun k => c k * (sig σ (k - 2) x * sig σ (k - 1) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - -2 - 2 = i from by ring, show i - -2 - 1 = i + 1 from by ring,
        show i - -2 = i + 2 from by ring])
  have r4 : ∑ k : ZMod n, (algebraMap K F w * c k) * (sig σ (k + 2) x * sig σ (k + 1) y)
      = ∑ i : ZMod n, (algebraMap K F w * c (i - 2)) * (sig σ i x * sig σ (i - 1) y) := by
    rw [← sum_reindex 2 (fun k => (algebraMap K F w * c k) * (sig σ (k + 2) x * sig σ (k + 1) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - 2 + 2 = i from by ring, show i - 2 + 1 = i - 1 from by ring])
  have r5 : ∑ k : ZMod n, (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k + 1) y)
      = ∑ i : ZMod n, (algebraMap K F w * c (i + 1)) * (sig σ i x * sig σ (i + 2) y) := by
    rw [← sum_reindex (-1)
      (fun k => (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k + 1) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - -1 - 1 = i from by ring, show i - -1 + 1 = i + 2 from by ring,
        show i - -1 = i + 1 from by ring])
  have r6 : ∑ k : ZMod n, (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k - 2) y)
      = ∑ i : ZMod n, (algebraMap K F w * c (i + 1)) * (sig σ i x * sig σ (i - 1) y) := by
    rw [← sum_reindex (-1)
      (fun k => (algebraMap K F w * c k) * (sig σ (k - 1) x * sig σ (k - 2) y))]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show i - -1 - 1 = i from by ring, show i - -1 - 2 = i - 1 from by ring,
        show i - -1 = i + 1 from by ring])
  have hL : ∑ k : ZMod n, c k * sig σ k (famMul n σ w x y)
      = ∑ i : ZMod n, (c (i - 1) * (sig σ i x * sig σ (i + 1) y)
          + c (i - 1) * (sig σ i x * sig σ (i - 2) y)
          + c (i + 2) * (sig σ i x * sig σ (i + 1) y)
          + algebraMap K F w * c (i - 2) * (sig σ i x * sig σ (i - 1) y)
          + algebraMap K F w * c (i + 1) * (sig σ i x * sig σ (i + 2) y)
          + algebraMap K F w * c (i + 1) * (sig σ i x * sig σ (i - 1) y)) := by
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, r1, r2, r3, r4, r5, r6,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hL]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hrhs i]
  ring

end Expansions

section Numerals

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- For `n ≥ 5` the elements `1, 2, 3, 4` of `ZMod n` are nonzero. -/
lemma zmod_small_facts (hn5 : 5 ≤ n) :
    (1 : ZMod n) ≠ 0 ∧ (2 : ZMod n) ≠ 0 ∧ (3 : ZMod n) ≠ 0 ∧ (4 : ZMod n) ≠ 0 := by
  have key : ∀ k : ℕ, 0 < k → k < 5 → ((k : ℕ) : ZMod n) ≠ 0 := by
    intro k hk0 hk
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hk0 hd
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using key 1 (by norm_num) (by norm_num)
  · simpa using key 2 (by norm_num) (by norm_num)
  · simpa using key 3 (by norm_num) (by norm_num)
  · simpa using key 4 (by norm_num) (by norm_num)

omit [NeZero n] in
/-- **The support lemma.** If a function on `ZMod n` vanishes at `j + u` for every
`u ∈ I = {1, 2, -1, -2}` and every `j ∉ I`, then it is supported at `0`.  This is the
translation argument of the proof of `thm:direct-nuclei`: a translation stabilising the
four-element set `I` has order dividing both `4` and `n`. -/
lemma support_at_zero {F : Type*} [Field F] (hn5 : 5 ≤ n) (hcop : Nat.Coprime 4 n)
    (c : ZMod n → F)
    (h : ∀ j : ZMod n, (j ≠ 1 ∧ j ≠ 2 ∧ j ≠ -1 ∧ j ≠ -2) →
       c (j + 1) = 0 ∧ c (j + 2) = 0 ∧ c (j - 1) = 0 ∧ c (j - 2) = 0) :
    ∀ m : ZMod n, m ≠ 0 → c m = 0 := by
  obtain ⟨z1, z2, z3, z4⟩ := zmod_small_facts hn5
  have hne12 : (1 : ZMod n) ≠ 2 := fun hh => z1 (by linear_combination -hh)
  have hne1m1 : (1 : ZMod n) ≠ -1 := fun hh => z2 (by linear_combination hh)
  have hne1m2 : (1 : ZMod n) ≠ -2 := fun hh => z3 (by linear_combination hh)
  have hne2m1 : (2 : ZMod n) ≠ -1 := fun hh => z3 (by linear_combination hh)
  have hne2m2 : (2 : ZMod n) ≠ -2 := fun hh => z4 (by linear_combination hh)
  have hnem1m2 : (-1 : ZMod n) ≠ -2 := fun hh => z1 (by linear_combination hh)
  intro m hm0
  by_contra hcm
  set I : Finset (ZMod n) := {1, 2, -1, -2} with hI
  have hmem : ∀ u ∈ I, m - u ∈ I := by
    intro u hu
    by_contra hnot
    simp only [hI, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    obtain ⟨e1, e2, e3, e4⟩ := h (m - u) hnot
    simp only [hI, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hcm (by rw [show m - 1 + 1 = m from by ring] at e1; exact e1)
    · exact hcm (by rw [show m - 2 + 2 = m from by ring] at e2; exact e2)
    · exact hcm (by rw [show m - -1 - 1 = m from by ring] at e3; exact e3)
    · exact hcm (by rw [show m - -2 - 2 = m from by ring] at e4; exact e4)
  have hinj : Function.Injective (fun u : ZMod n => m - u) := fun a b hab => by simpa using hab
  have himg : I.image (fun u => m - u) = I :=
    Finset.eq_of_subset_of_card_le (fun v hv => by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv; exact hmem u hu)
      (le_of_eq (Finset.card_image_of_injective I hinj).symm)
  have hsum : ∑ u ∈ I, (m - u) = ∑ v ∈ I, v := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  have hcard : I.card = 4 := by
    rw [hI, Finset.card_insert_of_notMem (by simp [hne12, hne1m1, hne1m2]),
      Finset.card_insert_of_notMem (by simp [hne2m1, hne2m2]),
      Finset.card_insert_of_notMem (by simp [hnem1m2]), Finset.card_singleton]
  have hzero : ∑ v ∈ I, v = 0 := by
    rw [hI, Finset.sum_insert (by simp [hne12, hne1m1, hne1m2]),
      Finset.sum_insert (by simp [hne2m1, hne2m2]),
      Finset.sum_insert (by simp [hnem1m2]), Finset.sum_singleton]
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, hzero, sub_zero] at hsum
  have h4m : (4 : ZMod n) * m = 0 := by
    have : (4 : ℕ) • m = (0 : ZMod n) := by rw [hsum]
    simpa [nsmul_eq_mul] using this
  have hu4 : IsUnit (4 : ZMod n) := by
    have h44 : ((4 : ℕ) : ZMod n) = (4 : ZMod n) := by push_cast; ring
    rw [← h44, ZMod.isUnit_iff_coprime]
    exact hcop
  refine hm0 ?_
  obtain ⟨v, hv⟩ := hu4.exists_left_inv
  calc m = v * ((4 : ZMod n) * m) := by rw [← mul_assoc, hv, one_mul]
  _ = 0 := by rw [h4m, mul_zero]

end Numerals

section SpreadSets

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} [NeZero n] {σ : F ≃ₐ[K] F} {w : K}

lemma famMul_add_left (x₁ x₂ y : F) :
    famMul n σ w (x₁ + x₂) y = famMul n σ w x₁ y + famMul n σ w x₂ y :=
  ((famMulₗ n σ w).flip y).map_add x₁ x₂

lemma famMul_add_right (x y₁ y₂ : F) :
    famMul n σ w x (y₁ + y₂) = famMul n σ w x y₁ + famMul n σ w x y₂ :=
  (famMulₗ n σ w x).map_add y₁ y₂

lemma famMul_smul_left (c : K) (x y : F) :
    famMul n σ w (algebraMap K F c * x) y = algebraMap K F c * famMul n σ w x y := by
  have h := ((famMulₗ n σ w).flip y).map_smul c x
  simpa [Algebra.smul_def] using h

lemma famMul_smul_right (c : K) (x y : F) :
    famMul n σ w x (algebraMap K F c * y) = algebraMap K F c * famMul n σ w x y := by
  have h := (famMulₗ n σ w x).map_smul c y
  simpa [Algebra.smul_def] using h

/-- The spread set `𝒞 = {R_y}` of the family. -/
def famC (n : ℕ) [NeZero n] (σ : F ≃ₐ[K] F) (w : K) : Set (F →+ F) :=
  spreadSet (famMul n σ w) (fun _ _ _ => famMul_add_left _ _ _)

/-- The dual spread set `𝒞^d = {L_x}` of the family. -/
def famCd (n : ℕ) [NeZero n] (σ : F ≃ₐ[K] F) (w : K) : Set (F →+ F) :=
  dualSpreadSet (famMul n σ w) (fun _ _ _ => famMul_add_right _ _ _)

/-- The set of `K`-scalar multiplications `m_a` (`a ∈ K`) of `F`. -/
def scalarMaps (K F : Type*) [Field K] [Field F] [Algebra K F] : Set (F →+ F) :=
  {T | ∃ a : K, ∀ x : F, T x = algebraMap K F a * x}

lemma mem_leftIdealiser_famCd {T : F →+ F} :
    T ∈ leftIdealiser (famCd n σ w) ↔
      ∀ x : F, ∃ x' : F, ∀ y : F, T (famMul n σ w x y) = famMul n σ w x' y := by
  constructor
  · intro hT x
    obtain ⟨x', hx'⟩ := hT _ ⟨x, rfl⟩
    exact ⟨x', fun y => (DFunLike.congr_fun hx' y).symm⟩
  · intro h U hU
    obtain ⟨x, rfl⟩ := hU
    obtain ⟨x', hx'⟩ := h x
    exact ⟨x', by ext y; exact (hx' y).symm⟩

lemma mem_leftIdealiser_famC {T : F →+ F} :
    T ∈ leftIdealiser (famC n σ w) ↔
      ∀ y : F, ∃ y' : F, ∀ x : F, T (famMul n σ w x y) = famMul n σ w x y' := by
  constructor
  · intro hT y
    obtain ⟨y', hy'⟩ := hT _ ⟨y, rfl⟩
    exact ⟨y', fun x => (DFunLike.congr_fun hy' x).symm⟩
  · intro h U hU
    obtain ⟨y, rfl⟩ := hU
    obtain ⟨y', hy'⟩ := h y
    exact ⟨y', by ext x; exact (hy' x).symm⟩

lemma mem_rightIdealiser_famC {T : F →+ F} :
    T ∈ rightIdealiser (famC n σ w) ↔
      ∀ y : F, ∃ y' : F, ∀ x : F, famMul n σ w (T x) y = famMul n σ w x y' := by
  constructor
  · intro hT y
    obtain ⟨y', hy'⟩ := hT _ ⟨y, rfl⟩
    exact ⟨y', fun x => (DFunLike.congr_fun hy' x).symm⟩
  · intro h U hU
    obtain ⟨y, rfl⟩ := hU
    obtain ⟨y', hy'⟩ := h y
    exact ⟨y', by ext x; exact (hy' x).symm⟩

variable (hP : IsPresemifield K (famMulₗ n σ w))
include hP

lemma famMul_left_cancel {u v : F} (h : ∀ y, famMul n σ w u y = famMul n σ w v y) : u = v := by
  have h0 : famMul n σ w (u - v) 1 = 0 := by
    have hs := ((famMulₗ n σ w).flip (1 : F)).map_sub u v
    simp only [LinearMap.flip_apply, famMulₗ_apply] at hs
    rw [hs, h 1, sub_self]
  rcases hP.eq_zero_or_eq_zero _ _ h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 one_ne_zero

lemma famMul_right_cancel {u v : F} (h : ∀ x, famMul n σ w x u = famMul n σ w x v) : u = v := by
  have h0 : famMul n σ w 1 (u - v) = 0 := by
    have := (famMulₗ n σ w 1).map_sub u v
    simp only [famMulₗ_apply] at this
    rw [this, h 1, sub_self]
  rcases hP.eq_zero_or_eq_zero _ _ h0 with h1 | h1
  · exact absurd h1 one_ne_zero
  · exact sub_eq_zero.mp h1

variable [FiniteDimensional K F]

lemma famMul_right_surjective {x : F} (hx : x ≠ 0) :
    Function.Surjective (fun y => famMul n σ w x y) := by
  have hinj : Function.Injective (famMulₗ n σ w x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rcases hP.eq_zero_or_eq_zero _ _ hy with h | h
    · exact absurd h hx
    · exact h
  exact (LinearMap.injective_iff_surjective.mp hinj)

lemma famMul_left_surjective {y : F} (hy : y ≠ 0) :
    Function.Surjective (fun x => famMul n σ w x y) := by
  have hinj : Function.Injective ((famMulₗ n σ w).flip y) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    simp only [LinearMap.flip_apply, famMulₗ_apply] at hx
    rcases hP.eq_zero_or_eq_zero _ _ hx with h | h
    · exact h
    · exact absurd h hy
  exact (LinearMap.injective_iff_surjective.mp hinj)

end SpreadSets

end Semifields
