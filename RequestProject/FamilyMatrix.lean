import RequestProject.Shift

/-!
# The split multiplication matrix of the new semifield family

For a parameter `w` with `w ^ 2 - w + 1 = 0` and split coordinates `X : ZMod n → R`, the
paper's matrix `L_w(X)` (equation `eq:family-entries`) has, in row `i`, the entries

* `(i, i+2) = X (i+1)`,
* `(i, i+1) = w * (X (i+2) + X (i-1))`,
* `(i, i-1) = X (i+1) + X (i-2)`,
* `(i, i-2) = w * X (i-1)`,

and all other entries zero.  Its rows are the split output forms `eq:family-split` of the
multiplication `eq:construction`.

The main results of this file are the matrix factorization `eq:factorization` and the
determinant formula `eq:leftdet`:
`det (LwM w X) = (1 + w ^ n) ^ 2 * (1 - w ^ (2 * n)) * ∏ i, X i`.
-/

namespace Semifields

open scoped BigOperators
open Matrix

variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- The split multiplication matrix `L_w(X)` of the family. -/
def LwM (w : R) (X : ZMod n → R) : Matrix (ZMod n) (ZMod n) R :=
  shiftM 2 (fun i => X (i + 1)) + shiftM 1 (fun i => w * (X (i + 2) + X (i - 1)))
    + shiftM (-1) (fun i => X (i + 1) + X (i - 2)) + shiftM (-2) (fun i => w * X (i - 1))

lemma shiftM_mulVec (a : ZMod n) (t Y : ZMod n → R) (i : ZMod n) :
    (shiftM a t).mulVec Y i = t i * Y (i + a) := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i + a)]
  · simp
  · intro k _ hk; simp [hk]
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- The rows of `LwM w X` applied to `Y` are the split output forms `f_i` of the paper. -/
lemma LwM_mulVec (w : R) (X Y : ZMod n → R) (i : ZMod n) :
    (LwM w X).mulVec Y i =
      X (i + 1) * Y (i + 2) + X (i + 1) * Y (i - 1) + X (i - 2) * Y (i - 1)
        + w * (X (i + 2) * Y (i + 1) + X (i - 1) * Y (i + 1) + X (i - 1) * Y (i - 2)) := by
  simp only [LwM, Matrix.add_mulVec, Pi.add_apply, shiftM_mulVec]
  have h1 : i + -1 = i - 1 := by ring
  have h2 : i + -2 = i - 2 := by ring
  rw [h1, h2]
  ring

omit [NeZero n] in
/-- `LwM` commutes with ring homomorphisms. -/
lemma map_LwM {S : Type*} [CommRing S] (f : R →+* S) (w : R) (X : ZMod n → R) :
    (LwM w X).map f = LwM (f w) (fun i => f (X i)) := by
  ext i j
  simp only [LwM, Matrix.map_apply, Matrix.add_apply, shiftM_apply]
  split_ifs <;> simp

section Field

variable {E : Type*} [Field E]

/-- Products over `ZMod n` are invariant under shifting the index. -/
lemma prod_shift (c : ZMod n) (X : ZMod n → E) : ∏ i, X (i + c) = ∏ i, X i :=
  Fintype.prod_equiv (Equiv.addRight c) (fun i => X (i + c)) X (fun _ => rfl)

variable (w : E) (X : ZMod n → E)

/-- The factor `H` of `eq:factorization`. -/
def facH : Matrix (ZMod n) (ZMod n) E := shiftM 0 (fun i => X (i - 1) * X (i + 1))

/-- The factor `B + w I` of `eq:factorization`. -/
def facB : Matrix (ZMod n) (ZMod n) E :=
  w • (1 : Matrix (ZMod n) (ZMod n) E) + shiftM 1 (fun i => X (i + 2) / X (i - 1))

/-- The factor `I - w ^ 2 B⁻¹ Π⁻¹` of `eq:factorization`. -/
def facC : Matrix (ZMod n) (ZMod n) E :=
  (1 : E) • (1 : Matrix (ZMod n) (ZMod n) E)
    + shiftM (-2) (fun i => -w ^ 2 * (X (i - 2) / X (i + 1)))

/-- The factor `Π + w I` of `eq:factorization`. -/
def facP : Matrix (ZMod n) (ZMod n) E :=
  w • (1 : Matrix (ZMod n) (ZMod n) E) + shiftM 1 (fun _ => 1)

variable {w X}

private lemma stage1 (hX : ∀ i, X i ≠ 0) :
    facH X * facB w X = shiftM (1 : ZMod n) (fun i => X (i + 1) * X (i + 2))
      + shiftM (0 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1))) := by
  rw [facH, facB, smul_one_eq_shiftM, mul_add, shiftM_mul, shiftM_mul, add_comm]
  congr 1
  · congr 1
    · ring
    · funext i
      simp only [add_zero]
      field_simp [hX]
  · congr 1
    · ring
    · funext i; ring

private lemma stage2 (hX : ∀ i, X i ≠ 0) (hw3 : w ^ 3 = -1) :
    (shiftM (1 : ZMod n) (fun i => X (i + 1) * X (i + 2))
        + shiftM (0 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1)))) * facC w X
      = shiftM (1 : ZMod n) (fun i => X (i + 1) * X (i + 2))
        + shiftM (0 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1)))
        + shiftM (-1 : ZMod n) (fun i => -w ^ 2 * (X (i - 1) * X (i + 1)))
        + shiftM (-2 : ZMod n) (fun i => X (i - 1) * X (i - 2)) := by
  rw [facC]
  simp only [smul_one_eq_shiftM, add_mul, mul_add, shiftM_mul, add_zero, mul_one,
    show ((1 : ZMod n) + -2) = -1 from by ring, show ((0 : ZMod n) + -2) = -2 from by ring]
  rw [← add_assoc]
  congr 1
  · congr 1
    apply shiftM_congr_fun
    intro i
    have h1 : i + 1 - 2 = i - 1 := by ring
    have h2 : i + 1 + 1 = i + 2 := by ring
    rw [h1, h2]
    field_simp [hX]
  · apply shiftM_congr_fun
    intro i
    field_simp [hX]
    linear_combination (-1 : E) * hw3

private lemma LwM_mul_diag :
    LwM w X * shiftM (0 : ZMod n) X
      = shiftM (2 : ZMod n) (fun i => X (i + 1) * X (i + 2))
        + shiftM (1 : ZMod n) (fun i => w * (X (i + 2) + X (i - 1)) * X (i + 1))
        + shiftM (-1 : ZMod n) (fun i => (X (i + 1) + X (i - 2)) * X (i - 1))
        + shiftM (-2 : ZMod n) (fun i => w * X (i - 1) * X (i - 2)) := by
  simp only [LwM, add_mul, shiftM_mul, add_zero, ← sub_eq_add_neg]

private lemma stage3 (hw3 : w ^ 3 = -1) :
    (shiftM (1 : ZMod n) (fun i => X (i + 1) * X (i + 2))
        + shiftM (0 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1)))
        + shiftM (-1 : ZMod n) (fun i => -w ^ 2 * (X (i - 1) * X (i + 1)))
        + shiftM (-2 : ZMod n) (fun i => X (i - 1) * X (i - 2))) * facP w
    = LwM w X * shiftM (0 : ZMod n) X := by
  have e1 : shiftM (1 : ZMod n) (fun i => X (i + 1) * X (i + 2) * w)
      + shiftM (1 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1)))
      = shiftM (1 : ZMod n) (fun i => w * X (i + 2) * X (i + 1) + w * X (i - 1) * X (i + 1)) := by
    rw [shiftM_add]; apply shiftM_congr_fun; intro i; ring
  have e2 : shiftM (0 : ZMod n) (fun i => w * (X (i - 1) * X (i + 1)) * w)
      + shiftM (0 : ZMod n) (fun i => -w ^ 2 * (X (i - 1) * X (i + 1))) = 0 := by
    rw [shiftM_add, shiftM_congr_fun (0 : ZMod n) (u := fun _ => (0 : E)) (fun i => by ring),
      shiftM_zero_fun]
  have e3 : shiftM (-1 : ZMod n) (fun i => -w ^ 2 * (X (i - 1) * X (i + 1)) * w)
      + shiftM (-1 : ZMod n) (fun i => X (i - 1) * X (i - 2))
      = shiftM (-1 : ZMod n) (fun i => X (i + 1) * X (i - 1) + X (i - 2) * X (i - 1)) := by
    rw [shiftM_add]; apply shiftM_congr_fun; intro i
    linear_combination (-(X (i - 1) * X (i + 1))) * hw3
  have e4 : shiftM (-2 : ZMod n) (fun i => X (i - 1) * X (i - 2) * w)
      = shiftM (-2 : ZMod n) (fun i => w * X (i - 1) * X (i - 2)) := by
    apply shiftM_congr_fun; intro i; ring
  rw [LwM_mul_diag, facP]
  simp only [smul_one_eq_shiftM, add_mul, mul_add, shiftM_mul, add_zero, mul_one,
    show ((1 : ZMod n) + 1) = 2 from by ring, show ((0 : ZMod n) + 1) = 1 from by ring,
    show ((-1 : ZMod n) + 1) = 0 from by ring, show ((-2 : ZMod n) + 1) = -1 from by ring]
  calc
    ((((shiftM (1 : ZMod n) fun i => X (i + 1) * X (i + 2) * w)
          + shiftM (0 : ZMod n) fun i => w * (X (i - 1) * X (i + 1)) * w)
          + shiftM (-1 : ZMod n) fun i => -w ^ 2 * (X (i - 1) * X (i + 1)) * w)
          + shiftM (-2 : ZMod n) fun i => X (i - 1) * X (i - 2) * w)
        + ((((shiftM (2 : ZMod n) fun i => X (i + 1) * X (i + 2))
          + shiftM (1 : ZMod n) fun i => w * (X (i - 1) * X (i + 1)))
          + shiftM (0 : ZMod n) fun i => -w ^ 2 * (X (i - 1) * X (i + 1)))
          + shiftM (-1 : ZMod n) fun i => X (i - 1) * X (i - 2))
      = (shiftM (2 : ZMod n) fun i => X (i + 1) * X (i + 2))
        + ((shiftM (1 : ZMod n) fun i => X (i + 1) * X (i + 2) * w)
          + shiftM (1 : ZMod n) fun i => w * (X (i - 1) * X (i + 1)))
        + ((shiftM (0 : ZMod n) fun i => w * (X (i - 1) * X (i + 1)) * w)
          + shiftM (0 : ZMod n) fun i => -w ^ 2 * (X (i - 1) * X (i + 1)))
        + ((shiftM (-1 : ZMod n) fun i => -w ^ 2 * (X (i - 1) * X (i + 1)) * w)
          + shiftM (-1 : ZMod n) fun i => X (i - 1) * X (i - 2))
        + (shiftM (-2 : ZMod n) fun i => X (i - 1) * X (i - 2) * w) := by abel
    _ = _ := by rw [e1, e2, e3, e4, add_zero]

/-- **The matrix factorization `eq:factorization`.**
`L_w(X) D = H (B + wI) (I - w² B⁻¹ Π⁻¹) (Π + wI)`, where `D = diag (X i)`. -/
theorem LwM_factorization (hX : ∀ i, X i ≠ 0) (hw3 : w ^ 3 = -1) :
    LwM w X * shiftM (0 : ZMod n) X = facH X * facB w X * facC w X * facP w := by
  rw [stage1 hX, stage2 hX hw3, stage3 hw3]

lemma det_facH : (facH X).det = (∏ i, X i) ^ 2 := by
  rw [facH, det_shiftM_zero, Finset.prod_mul_distrib]
  rw [show (fun i : ZMod n => X (i - 1)) = (fun i : ZMod n => X (i + (-1))) from by
      funext i; rw [sub_eq_add_neg]]
  rw [prod_shift (-1) X, prod_shift 1 X, sq]

lemma det_facB (hX : ∀ i, X i ≠ 0) (hodd : Odd n) (h3 : 3 ≤ n) :
    (facB w X).det = w ^ n + 1 := by
  have h1 : IsUnit (1 : ZMod n) := isUnit_one
  have h1' : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ ((0 : ℕ) : ZMod n) := by
      rw [Ne, ZMod.natCast_eq_natCast_iff]
      simp [Nat.ModEq]
      omega
    simpa using this
  rw [facB, det_smul_one_add_shiftM w h1 h1' hodd]
  congr 1
  rw [Finset.prod_div_distrib]
  rw [show (fun i : ZMod n => X (i - 1)) = (fun i : ZMod n => X (i + (-1))) from by
      funext i; rw [sub_eq_add_neg]]
  rw [prod_shift 2 X, prod_shift (-1) X]
  exact div_self (Finset.prod_ne_zero_iff.mpr (fun i _ => hX i))

lemma det_facP (hodd : Odd n) (h3 : 3 ≤ n) : (facP (n := n) w).det = w ^ n + 1 := by
  have h1 : IsUnit (1 : ZMod n) := isUnit_one
  have h1' : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ ((0 : ℕ) : ZMod n) := by
      rw [Ne, ZMod.natCast_eq_natCast_iff]
      simp [Nat.ModEq]
      omega
    simpa using this
  rw [facP, det_smul_one_add_shiftM w h1 h1' hodd]
  simp

lemma det_facC (hX : ∀ i, X i ≠ 0) (hodd : Odd n) (h3 : 3 ≤ n) :
    (facC w X).det = 1 - w ^ (2 * n) := by
  have h2 : IsUnit (-2 : ZMod n) := by
    refine IsUnit.neg ?_
    have : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
    rw [← this, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr hodd
  have h2' : (-2 : ZMod n) ≠ 0 := by
    intro hcon
    have : ((2 : ℕ) : ZMod n) = 0 := by
      have : (2 : ZMod n) = 0 := by linear_combination -hcon
      simpa using this
    have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp this
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [facC, det_smul_one_add_shiftM (1 : E) h2 h2' hodd]
  have hprod : ∏ i : ZMod n, (-w ^ 2 * (X (i - 2) / X (i + 1))) = -w ^ (2 * n) := by
    rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
    rw [show (fun i : ZMod n => X (i - 2)) = (fun i : ZMod n => X (i + (-2))) from by
        funext i; rw [sub_eq_add_neg]]
    rw [prod_shift (-2) X, prod_shift 1 X,
      div_self (Finset.prod_ne_zero_iff.mpr (fun i _ => hX i)), mul_one,
      Finset.prod_const, Finset.card_univ, ZMod.card]
    rw [show (-w ^ 2 : E) = (-1) * w ^ 2 from by ring, mul_pow, ← pow_mul, hodd.neg_one_pow]
    ring_nf
  rw [hprod, one_pow]
  ring

/-- **The split left determinant `eq:leftdet`**, at a point with all coordinates nonzero. -/
theorem det_LwM_of_ne_zero (hX : ∀ i, X i ≠ 0) (hw : w ^ 2 - w + 1 = 0)
    (hodd : Odd n) (h3 : 3 ≤ n) :
    (LwM w X).det = (1 + w ^ n) ^ 2 * (1 - w ^ (2 * n)) * ∏ i, X i := by
  have hw3 : w ^ 3 = -1 := by linear_combination (w + 1) * hw
  have hprodX : (∏ i, X i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hX i)
  have hfac := congrArg Matrix.det (LwM_factorization hX hw3)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_shiftM_zero,
    det_facH, det_facB hX hodd h3, det_facC hX hodd h3, det_facP hodd h3] at hfac
  have : (LwM w X).det * ∏ i, X i
      = ((1 + w ^ n) ^ 2 * (1 - w ^ (2 * n)) * ∏ i, X i) * ∏ i, X i := by
    rw [hfac]; ring
  exact mul_right_cancel₀ hprodX this


/-- **The split left determinant `eq:leftdet` as a polynomial identity.**  In the
polynomial ring `E[X_i : i ∈ ZMod n]`,
`det L_w(X) = (1 + w^n)^2 (1 - w^{2n}) ∏ X_i`. -/
theorem det_LwM_mvpoly (w : E) (hw : w ^ 2 - w + 1 = 0) (hodd : Odd n) (h3 : 3 ≤ n) :
    (LwM (MvPolynomial.C w) (fun i => MvPolynomial.X (R := E) i)).det
      = MvPolynomial.C ((1 + w ^ n) ^ 2 * (1 - w ^ (2 * n))) * ∏ i : ZMod n, MvPolynomial.X (R := E) i := by
  set A := MvPolynomial (ZMod n) E
  set f := algebraMap A (FractionRing A) with hf
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective A (FractionRing A)
  apply hinj
  have hmapdet := RingHom.map_det f (LwM (MvPolynomial.C w) (fun i => MvPolynomial.X (R := E) i))
  rw [hmapdet]
  have hmap : f.mapMatrix (LwM (MvPolynomial.C w) (fun i => MvPolynomial.X (R := E) i))
      = LwM (f (MvPolynomial.C w)) (fun i => f (MvPolynomial.X i)) := map_LwM f _ _
  rw [hmap]
  have hX : ∀ i : ZMod n, f (MvPolynomial.X (R := E) i) ≠ 0 := fun i =>
    fun h => MvPolynomial.X_ne_zero i (hinj (by simpa using h))
  have hw' : (f (MvPolynomial.C w)) ^ 2 - (f (MvPolynomial.C w)) + 1 = 0 := by
    rw [← map_pow, ← map_one f, ← map_sub, ← map_add, ← map_zero f]
    exact congrArg f (by rw [← map_one MvPolynomial.C, ← map_pow, ← map_sub, ← map_add,
      ← map_zero (MvPolynomial.C (σ := ZMod n))]; exact congrArg _ hw)
  rw [det_LwM_of_ne_zero hX hw' hodd h3]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_prod]

end Field

end Semifields
