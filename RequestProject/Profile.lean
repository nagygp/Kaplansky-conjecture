import RequestProject.Basic

/-!
# Determinant forms of a bilinear multiplication and their behaviour under isotopy

For a `K`-bilinear multiplication `mul` on `K ^ n` we form the *structure tensor*
`c i j k` and the three *pencils* of `eq:three-matrices`,

* `L(X)_{k j} = ∑ i, X i * c i j k`  (left multiplication pencil),
* `R(X)_{k i} = ∑ j, X j * c i j k`  (right multiplication pencil),
* `T(X)_{i j} = ∑ k, X k * c i j k`  (transpose pencil),

whose determinants are the three *determinant forms* `D_L`, `D_R`, `D_tr` of
`subsec:determinants`, homogeneous polynomials of degree `n` in `MvPolynomial (Fin n) K`.

The main results of this file are the identities `eq:pencilisotopy`: a `K`-linear isotopism
`(A, B, C)` transforms each determinant form by an invertible linear substitution of the
variables and a nonzero scalar factor.
-/

namespace Semifields

open scoped BigOperators
open MvPolynomial Matrix

section Tensor

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The structure tensor of a bilinear multiplication on `K ^ n`, in the standard basis. -/
def structTensor (mul : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K))
    (i j k : Fin n) : K := mul (Pi.single i 1) (Pi.single j 1) k

/-- Every vector is the sum of its coordinates times the standard basis vectors. -/
lemma sum_single_smul (u : Fin n → K) : ∑ i, u i • (Pi.single i 1 : Fin n → K) = u := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]

/-- Coordinatewise expansion of a linear map in the standard basis. -/
lemma linear_apply_expand (T : (Fin n → K) →ₗ[K] (Fin n → K)) (z : Fin n → K) (k : Fin n) :
    T z k = ∑ p, z p * T (Pi.single p 1) k := by
  conv_lhs => rw [← sum_single_smul z]
  rw [map_sum]
  simp [Finset.sum_apply, smul_eq_mul]

/-- Coordinatewise expansion of a bilinear multiplication in the standard basis. -/
lemma mul_apply_expand (mul : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K))
    (u w : Fin n → K) (k : Fin n) :
    mul u w k = ∑ i, ∑ j, u i * w j * structTensor mul i j k := by
  have h1 : mul u w = ∑ i, ∑ j, (u i * w j) • mul (Pi.single i 1) (Pi.single j 1) := by
    conv_lhs => rw [← sum_single_smul u]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, LinearMap.smul_apply]
    conv_lhs => rw [← sum_single_smul w]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_smul]
  rw [h1]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, structTensor]

/-- The matrix of a linear endomorphism of `K ^ n` in the standard basis. -/
def matOf (T : (Fin n → K) →ₗ[K] (Fin n → K)) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => T (Pi.single j 1) i

/-- The scalar form of `eq:pencilisotopy`: the structure tensors of two isotopic
multiplications are related by the three matrices of the isotopism. -/
lemma tensor_isotopy {mulP mulQ : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)}
    {A B Cm : (Fin n → K) →ₗ[K] (Fin n → K)}
    (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (l m k : Fin n) :
    ∑ i, ∑ j, matOf A i l * matOf B j m * structTensor mulQ i j k
      = ∑ p, matOf Cm k p * structTensor mulP l m p := by
  have h := congrFun (hiso (Pi.single l 1) (Pi.single m 1)) k
  rw [mul_apply_expand, linear_apply_expand] at h
  simp only [matOf, Matrix.of_apply]
  rw [h]
  exact Finset.sum_congr rfl (fun p _ => by rw [structTensor]; ring)

end Tensor

section Pencils

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The left multiplication pencil `L(X)`. -/
noncomputable def pencilL (c : Fin n → Fin n → Fin n → K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun k j => ∑ i, MvPolynomial.X i * MvPolynomial.C (c i j k)

/-- The transpose pencil `T(X)`. -/
noncomputable def pencilT (c : Fin n → Fin n → Fin n → K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (c i j k)

/-- The transposed structure tensor; the right pencil is the left pencil of this tensor. -/
def flipT (c : Fin n → Fin n → Fin n → K) : Fin n → Fin n → Fin n → K := fun i j k => c j i k

/-- The right multiplication pencil `R(X)`. -/
noncomputable def pencilR (c : Fin n → Fin n → Fin n → K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) := pencilL (flipT c)

/-- The left determinant form `D_L`. -/
noncomputable def detFormL (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) K := (pencilL c).det

/-- The right determinant form `D_R`. -/
noncomputable def detFormR (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) K := (pencilR c).det

/-- The transpose determinant form `D_tr`. -/
noncomputable def detFormT (c : Fin n → Fin n → Fin n → K) : MvPolynomial (Fin n) K := (pencilT c).det

/-- The algebra endomorphism of `K[X_0, …, X_{n-1}]` substituting `X i ↦ ∑ j, S i j X j`. -/
noncomputable def substHom (S : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.C (S i j) * MvPolynomial.X j

@[simp] lemma substHom_X (S : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    substHom S (MvPolynomial.X i) = ∑ j, MvPolynomial.C (S i j) * MvPolynomial.X j := by
  simp [substHom]

lemma flipT_structTensor (mul : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)) :
    flipT (structTensor mul) = structTensor mul.flip := by
  funext i j k
  rfl

end Pencils

section Isotopy

variable {K : Type*} [CommRing K] {n : ℕ}

/-- A triple sum may be reordered, moving the innermost index outermost. -/
private lemma sum3_comm {M ι : Type*} [AddCommMonoid M] [Fintype ι] (T : ι → ι → ι → M) :
    ∑ a, ∑ b, ∑ c, T a b c = ∑ c, ∑ a, ∑ b, T a b c := by
  calc ∑ a, ∑ b, ∑ c, T a b c = ∑ a, ∑ c, ∑ b, T a b c :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  _ = ∑ c, ∑ a, ∑ b, T a b c := Finset.sum_comm

lemma matOf_comp (S T : (Fin n → K) →ₗ[K] (Fin n → K)) :
    matOf (S ∘ₗ T) = matOf S * matOf T := by
  ext i j
  simp only [matOf, Matrix.of_apply, Matrix.mul_apply, LinearMap.comp_apply]
  rw [linear_apply_expand S (T (Pi.single j 1)) i]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma matOf_id : matOf (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
  ext i j
  simp [matOf, Matrix.one_apply, Pi.single_apply]

/-- The matrix of a linear automorphism has unit determinant. -/
lemma isUnit_det_matOf (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    IsUnit (matOf (e : (Fin n → K) →ₗ[K] (Fin n → K))).det := by
  have h : matOf (e : (Fin n → K) →ₗ[K] (Fin n → K)) * matOf (e.symm : _ →ₗ[K] _) = 1 := by
    rw [← matOf_comp]
    have hid : ((e : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (e.symm : _ →ₗ[K] _)) = LinearMap.id := by
      ext x
      simp
    rw [hid, matOf_id]
  exact Matrix.isUnit_det_of_right_inverse h

variable {Ω : Type*} [CommRing Ω] [Algebra K Ω]

/-- The left pencil, evaluated at a point of `Ω ^ n`. -/
def pencilLat (c : Fin n → Fin n → Fin n → K) (v : Fin n → Ω) : Matrix (Fin n) (Fin n) Ω :=
  Matrix.of fun k j => ∑ i, v i * algebraMap K Ω (c i j k)

/-- The transpose pencil, evaluated at a point of `Ω ^ n`. -/
def pencilTat (c : Fin n → Fin n → Fin n → K) (v : Fin n → Ω) : Matrix (Fin n) (Fin n) Ω :=
  Matrix.of fun i j => ∑ k, v k * algebraMap K Ω (c i j k)

/-- The right pencil, evaluated at a point of `Ω ^ n`. -/
def pencilRat (c : Fin n → Fin n → Fin n → K) (v : Fin n → Ω) : Matrix (Fin n) (Fin n) Ω :=
  pencilLat (flipT c) v

/-- The image of a point of `Ω ^ n` under a `K`-matrix. -/
def actOn (S : Matrix (Fin n) (Fin n) K) (v : Fin n → Ω) : Fin n → Ω :=
  fun i => ∑ l, algebraMap K Ω (S i l) * v l

variable {mulP mulQ : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)}
  {A B Cm : (Fin n → K) →ₗ[K] (Fin n → K)}

/-- **`eq:pencilisotopy`, left form.**  If `(A, B, C)` is a `K`-linear isotopism from
`mulP` to `mulQ`, then `L_Q(Av) · B = C · L_P(v)` at every point `v` of every commutative
`K`-algebra. -/
theorem pencilLat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (v : Fin n → Ω) :
    pencilLat (structTensor mulQ) (actOn (matOf A) v) * ((matOf B).map (algebraMap K Ω))
      = ((matOf Cm).map (algebraMap K Ω)) * pencilLat (structTensor mulP) v := by
  ext k m
  simp only [Matrix.mul_apply, Matrix.map_apply, pencilLat, Matrix.of_apply, actOn]
  calc ∑ j, (∑ i, (∑ l, algebraMap K Ω (matOf A i l) * v l)
              * algebraMap K Ω (structTensor mulQ i j k)) * algebraMap K Ω (matOf B j m)
      = ∑ j, ∑ i, ∑ l, algebraMap K Ω (matOf A i l) * v l
              * algebraMap K Ω (structTensor mulQ i j k) * algebraMap K Ω (matOf B j m) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul, Finset.sum_mul])
  _ = ∑ l, ∑ j, ∑ i, algebraMap K Ω (matOf A i l) * v l
              * algebraMap K Ω (structTensor mulQ i j k) * algebraMap K Ω (matOf B j m) :=
        sum3_comm _
  _ = ∑ l, v l * algebraMap K Ω
        (∑ i, ∑ j, matOf A i l * matOf B j m * structTensor mulQ i j k) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [map_sum, map_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  _ = ∑ l, v l * algebraMap K Ω (∑ p, matOf Cm k p * structTensor mulP l m p) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [tensor_isotopy hiso l m k]
  _ = ∑ p, algebraMap K Ω (matOf Cm k p)
        * ∑ i, v i * algebraMap K Ω (structTensor mulP i m p) := by
        simp only [map_sum, map_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l _ => by ring))

/-- **`eq:pencilisotopy`, right form.** -/
theorem pencilRat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (v : Fin n → Ω) :
    pencilRat (structTensor mulQ) (actOn (matOf B) v) * ((matOf A).map (algebraMap K Ω))
      = ((matOf Cm).map (algebraMap K Ω)) * pencilRat (structTensor mulP) v := by
  have hiso' : ∀ x y, mulQ.flip (B x) (A y) = Cm (mulP.flip x y) := fun x y => hiso y x
  unfold pencilRat
  rw [flipT_structTensor, flipT_structTensor]
  exact pencilLat_isotopy hiso' v

/-- **`eq:pencilisotopy`, transpose form.** -/
theorem pencilTat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) (v : Fin n → Ω) :
    pencilTat (structTensor mulP) (actOn (matOf Cm).transpose v)
      = ((matOf A).transpose.map (algebraMap K Ω)) * pencilTat (structTensor mulQ) v
          * ((matOf B).map (algebraMap K Ω)) := by
  ext l m
  have hL : pencilTat (structTensor mulP) (actOn (matOf Cm).transpose v) l m
      = ∑ q, v q * algebraMap K Ω (∑ p, matOf Cm q p * structTensor mulP l m p) := by
    simp only [pencilTat, Matrix.of_apply, actOn, Matrix.transpose_apply]
    calc ∑ p, (∑ q, algebraMap K Ω (matOf Cm q p) * v q)
            * algebraMap K Ω (structTensor mulP l m p)
        = ∑ p, ∑ q, algebraMap K Ω (matOf Cm q p) * v q
            * algebraMap K Ω (structTensor mulP l m p) :=
          Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_mul])
    _ = ∑ q, ∑ p, algebraMap K Ω (matOf Cm q p) * v q
            * algebraMap K Ω (structTensor mulP l m p) := Finset.sum_comm
    _ = ∑ q, v q * algebraMap K Ω (∑ p, matOf Cm q p * structTensor mulP l m p) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          simp only [map_sum, map_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  have hR : (((matOf A).transpose.map (algebraMap K Ω)) * pencilTat (structTensor mulQ) v
      * ((matOf B).map (algebraMap K Ω))) l m
      = ∑ q, v q * algebraMap K Ω
          (∑ i, ∑ j, matOf A i l * matOf B j m * structTensor mulQ i j q) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, pencilTat, Matrix.of_apply,
      Matrix.transpose_apply]
    calc ∑ j, (∑ i, algebraMap K Ω (matOf A i l)
            * ∑ q, v q * algebraMap K Ω (structTensor mulQ i j q))
            * algebraMap K Ω (matOf B j m)
        = ∑ j, ∑ i, ∑ q, algebraMap K Ω (matOf A i l)
            * (v q * algebraMap K Ω (structTensor mulQ i j q))
            * algebraMap K Ω (matOf B j m) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum, Finset.sum_mul])
    _ = ∑ q, ∑ j, ∑ i, algebraMap K Ω (matOf A i l)
            * (v q * algebraMap K Ω (structTensor mulQ i j q))
            * algebraMap K Ω (matOf B j m) := sum3_comm _
    _ = ∑ q, v q * algebraMap K Ω
          (∑ i, ∑ j, matOf A i l * matOf B j m * structTensor mulQ i j q) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          simp only [map_sum, map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun q _ => by rw [tensor_isotopy hiso l m q])

end Isotopy

section DetForms

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The generic point: the pencil matrices are the evaluated pencils at `(X_0, …, X_{n-1})`. -/
lemma pencilL_eq_pencilLat (c : Fin n → Fin n → Fin n → K) :
    pencilL c = pencilLat c (fun i => MvPolynomial.X i) := by
  ext k j
  simp [pencilL, pencilLat, MvPolynomial.algebraMap_eq]

lemma pencilT_eq_pencilTat (c : Fin n → Fin n → Fin n → K) :
    pencilT c = pencilTat c (fun i => MvPolynomial.X i) := by
  ext k j
  simp [pencilT, pencilTat, MvPolynomial.algebraMap_eq]

lemma pencilR_eq_pencilRat (c : Fin n → Fin n → Fin n → K) :
    pencilR c = pencilRat c (fun i => MvPolynomial.X i) := by
  rw [pencilR, pencilRat, pencilL_eq_pencilLat]

lemma substHom_C (S : Matrix (Fin n) (Fin n) K) (a : K) :
    substHom S (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [substHom]

/-- Substituting `X ↦ S X` in a pencil is evaluation at the point `S X`. -/
lemma map_substHom_pencilL (c : Fin n → Fin n → Fin n → K) (S : Matrix (Fin n) (Fin n) K) :
    (pencilL c).map (substHom S) = pencilLat c (actOn S (fun i => MvPolynomial.X i)) := by
  ext k j
  simp only [Matrix.map_apply, pencilL, pencilLat, Matrix.of_apply, actOn, map_sum, map_mul,
    substHom_X, substHom_C, MvPolynomial.algebraMap_eq]

lemma map_substHom_pencilT (c : Fin n → Fin n → Fin n → K) (S : Matrix (Fin n) (Fin n) K) :
    (pencilT c).map (substHom S) = pencilTat c (actOn S (fun i => MvPolynomial.X i)) := by
  ext k j
  simp only [Matrix.map_apply, pencilT, pencilTat, Matrix.of_apply, actOn, map_sum, map_mul,
    substHom_X, substHom_C, MvPolynomial.algebraMap_eq]

lemma map_substHom_pencilR (c : Fin n → Fin n → Fin n → K) (S : Matrix (Fin n) (Fin n) K) :
    (pencilR c).map (substHom S) = pencilRat c (actOn S (fun i => MvPolynomial.X i)) :=
  map_substHom_pencilL _ _

variable {mulP mulQ : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)}
  {A B Cm : (Fin n → K) →ₗ[K] (Fin n → K)}

/-- **`eq:pencilisotopy` for the left determinant form.**  A `K`-linear isotopism `(A, B, C)`
transforms `D_L` by the substitution `X ↦ A X` and the nonzero scalar `det C / det B`. -/
theorem detFormL_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) :
    substHom (matOf A) (detFormL (structTensor mulQ)) * MvPolynomial.C (matOf B).det
      = MvPolynomial.C (matOf Cm).det * detFormL (structTensor mulP) := by
  have h := pencilLat_isotopy (Ω := MvPolynomial (Fin n) K) hiso (fun i => MvPolynomial.X i)
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, ← map_substHom_pencilL, ← pencilL_eq_pencilLat] at hdet
  have hmapP : ∀ (f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)
      (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K)), (M.map f).det = f M.det :=
    fun f M => (RingHom.map_det (f : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) M).symm
  have hmapC : ∀ M : Matrix (Fin n) (Fin n) K,
      (M.map (algebraMap K (MvPolynomial (Fin n) K))).det
        = algebraMap K (MvPolynomial (Fin n) K) M.det :=
    fun M => (RingHom.map_det (algebraMap K (MvPolynomial (Fin n) K)) M).symm
  rw [hmapP, hmapC, hmapC] at hdet
  simpa [detFormL, MvPolynomial.algebraMap_eq] using hdet

/-- **`eq:pencilisotopy` for the right determinant form.** -/
theorem detFormR_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) :
    substHom (matOf B) (detFormR (structTensor mulQ)) * MvPolynomial.C (matOf A).det
      = MvPolynomial.C (matOf Cm).det * detFormR (structTensor mulP) := by
  have hiso' : ∀ x y, mulQ.flip (B x) (A y) = Cm (mulP.flip x y) := fun x y => hiso y x
  have h := detFormL_isotopy hiso'
  rw [detFormR, detFormR, pencilR, pencilR, flipT_structTensor, flipT_structTensor]
  exact h

/-- **`eq:pencilisotopy` for the transpose determinant form.** -/
theorem detFormT_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y)) :
    substHom (matOf Cm).transpose (detFormT (structTensor mulP))
      = MvPolynomial.C (matOf A).det * detFormT (structTensor mulQ)
          * MvPolynomial.C (matOf B).det := by
  have h := pencilTat_isotopy (Ω := MvPolynomial (Fin n) K) hiso (fun i => MvPolynomial.X i)
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, ← map_substHom_pencilT, ← pencilT_eq_pencilTat] at hdet
  have hmapP : ∀ (f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)
      (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K)), (M.map f).det = f M.det :=
    fun f M => (RingHom.map_det (f : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) M).symm
  have hmapC : ∀ M : Matrix (Fin n) (Fin n) K,
      (M.map (algebraMap K (MvPolynomial (Fin n) K))).det
        = algebraMap K (MvPolynomial (Fin n) K) M.det :=
    fun M => (RingHom.map_det (algebraMap K (MvPolynomial (Fin n) K)) M).symm
  rw [hmapP, hmapC, hmapC, Matrix.det_transpose] at hdet
  simpa [detFormT, MvPolynomial.algebraMap_eq] using hdet

end DetForms

section Ranks

variable {K : Type*} [CommRing K] {n : ℕ} {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {mulP mulQ : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)}
  {A B Cm : (Fin n → K) →ₗ[K] (Fin n → K)}

private lemma det_map_algebraMap (M : Matrix (Fin n) (Fin n) K) :
    (M.map (algebraMap K Ω)).det = algebraMap K Ω M.det :=
  (RingHom.map_det (algebraMap K Ω) M).symm

/-- A `K`-linear isotopism preserves the rank of the left pencil at corresponding points. -/
theorem rank_pencilLat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y))
    (hB : IsUnit (matOf B).det) (hC : IsUnit (matOf Cm).det) (v : Fin n → Ω) :
    (pencilLat (structTensor mulQ) (actOn (matOf A) v)).rank
      = (pencilLat (structTensor mulP) v).rank := by
  have h := pencilLat_isotopy (Ω := Ω) hiso v
  have hBΩ : IsUnit ((matOf B).map (algebraMap K Ω)).det := by
    rw [det_map_algebraMap]; exact hB.map _
  have hCΩ : IsUnit ((matOf Cm).map (algebraMap K Ω)).det := by
    rw [det_map_algebraMap]; exact hC.map _
  calc (pencilLat (structTensor mulQ) (actOn (matOf A) v)).rank
      = (pencilLat (structTensor mulQ) (actOn (matOf A) v)
          * ((matOf B).map (algebraMap K Ω))).rank :=
        (Matrix.rank_mul_eq_left_of_isUnit_det _ _ hBΩ).symm
  _ = (((matOf Cm).map (algebraMap K Ω)) * pencilLat (structTensor mulP) v).rank := by rw [h]
  _ = (pencilLat (structTensor mulP) v).rank := Matrix.rank_mul_eq_right_of_isUnit_det _ _ hCΩ

/-- A `K`-linear isotopism preserves the rank of the right pencil at corresponding points. -/
theorem rank_pencilRat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y))
    (hA : IsUnit (matOf A).det) (hC : IsUnit (matOf Cm).det) (v : Fin n → Ω) :
    (pencilRat (structTensor mulQ) (actOn (matOf B) v)).rank
      = (pencilRat (structTensor mulP) v).rank := by
  have hiso' : ∀ x y, mulQ.flip (B x) (A y) = Cm (mulP.flip x y) := fun x y => hiso y x
  have h := rank_pencilLat_isotopy (Ω := Ω) hiso' hA hC v
  unfold pencilRat
  rw [flipT_structTensor, flipT_structTensor]
  exact h

/-- A `K`-linear isotopism preserves the rank of the transpose pencil at corresponding
points. -/
theorem rank_pencilTat_isotopy (hiso : ∀ x y, mulQ (A x) (B y) = Cm (mulP x y))
    (hA : IsUnit (matOf A).det) (hB : IsUnit (matOf B).det) (v : Fin n → Ω) :
    (pencilTat (structTensor mulP) (actOn (matOf Cm).transpose v)).rank
      = (pencilTat (structTensor mulQ) v).rank := by
  have h := pencilTat_isotopy (Ω := Ω) hiso v
  have hAΩ : IsUnit ((matOf A).transpose.map (algebraMap K Ω)).det := by
    rw [det_map_algebraMap, Matrix.det_transpose]; exact hA.map _
  have hBΩ : IsUnit ((matOf B).map (algebraMap K Ω)).det := by
    rw [det_map_algebraMap]; exact hB.map _
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hBΩ,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hAΩ]

end Ranks

end Semifields
