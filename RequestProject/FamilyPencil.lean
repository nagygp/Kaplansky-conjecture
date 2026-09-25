import RequestProject.Pencil
import RequestProject.VertexRank

/-!
# The split pencils of the family and of the generalized twisted fields

This file writes two split multiplication matrices as linear pencils in the sense of
`RequestProject.Pencil`:

* the matrix `L_w(X)` of the family (`eq:family-entries`), with pencil `lwP w`;
* the matrix `G(X) = diag(X) - (c_i X_{i+α})_{(i, i+β)}` of the multiplication
  `x ∘ y = x y - c · σ^α(x) · σ^β(y)` (the Albert generalized twisted field `eq:gtf`), with
  pencil `gtfP c α β`.

For both we compute the determinant as a polynomial identity valid at every point, and for
the family we prove the cyclic symmetry `eq:cyclic-tensor` of its trilinear form.
-/

namespace Semifields

open scoped BigOperators
open Matrix

variable {n : ℕ} [NeZero n]

section LwPencil

variable {F : Type*} [Field F]

/-- The coefficient matrices of the pencil `L_w(X)`. -/
noncomputable def lwP (w : F) (k : ZMod n) : Matrix (ZMod n) (ZMod n) F :=
  LwM w (Pi.single k 1)

lemma LwM_apply_eq_sum {R : Type*} [CommRing R] (w : R) (X : ZMod n → R) (i j : ZMod n) :
    LwM w X i j = ∑ k, X k * LwM w (Pi.single k 1) i j := by
  simp only [LwM, Matrix.add_apply, shiftM_apply]
  split_ifs <;> simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_comm]

/-- `L_w(X)` is the pencil `lwP w`, over every `F`-algebra. -/
lemma LwM_eq_pen {R : Type*} [CommRing R] [Algebra F R] (w : F) (Y : ZMod n → R) :
    LwM (algebraMap F R w) Y = pen (lwP w) Y := by
  ext i j
  rw [pen_apply, LwM_apply_eq_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  have h := map_LwM (algebraMap F R) w (Pi.single k (1 : F))
  have h2 : (fun i : ZMod n => algebraMap F R ((Pi.single k (1 : F) : ZMod n → F) i))
      = (Pi.single k 1 : ZMod n → R) := by
    funext l; simp [Pi.single_apply, apply_ite (algebraMap F R)]
  rw [h2] at h
  rw [lwP, ← h]
  rfl

lemma pen_lwP_self (w : F) (X : ZMod n → F) : pen (lwP w) X = LwM w X := by
  rw [← LwM_eq_pen]; rfl

/-- **The left determinant of the family at every polynomial point.** -/
theorem det_pen_lwP (w : F) (hw : w ^ 2 - w + 1 = 0) (hodd : Odd n) (h3 : 3 ≤ n)
    (Y : ZMod n → MvPolynomial (ZMod n) F) :
    (pen (lwP w) Y).det
      = MvPolynomial.C ((1 + w ^ n) ^ 2 * (1 - w ^ (2 * n))) * ∏ i, Y i := by
  have hX := det_LwM_mvpoly w hw hodd h3
  have := congrArg (MvPolynomial.aeval (R := F) Y) hX
  rw [AlgHom.map_det] at this
  rw [← LwM_eq_pen, MvPolynomial.algebraMap_eq]
  have hmap : (MvPolynomial.aeval Y).mapMatrix
      (LwM (MvPolynomial.C w) (fun i => MvPolynomial.X (R := F) i))
      = LwM (MvPolynomial.C w) Y := by
    have h := map_LwM (MvPolynomial.aeval (R := F) Y).toRingHom (MvPolynomial.C w)
      (fun i => MvPolynomial.X (R := F) i)
    rw [AlgHom.mapMatrix_apply]
    refine h.trans ?_
    simp
  rw [hmap] at this
  rw [this]
  simp [map_prod]

/-- **Cyclic symmetry `eq:cyclic-tensor`** of the split trilinear form of the family. -/
theorem pencilCyclic_lwP (w : F) : PencilCyclic (lwP (n := n) w) := by
  intro X Y Z
  rw [pen_lwP_self, pen_lwP_self]
  simp only [dotProduct, LwM_mulVec, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ i, Z i * (X (i + 1) * Y (i + 2)) = ∑ i, X i * (Y (i + 1) * Z (i - 1)) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.coe_addRight]; ring_nf)
  have e2 : ∑ i, Z i * (X (i + 1) * Y (i - 1)) = ∑ i, X i * (Y (i - 2) * Z (i - 1)) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.coe_addRight]; ring_nf)
  have e3 : ∑ i, Z i * (X (i - 2) * Y (i - 1)) = ∑ i, X i * (Y (i + 1) * Z (i + 2)) :=
    Fintype.sum_equiv (Equiv.subRight (2 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.subRight_apply]; ring_nf)
  have e4 : ∑ i, Z i * (w * (X (i + 2) * Y (i + 1)))
      = ∑ i, X i * (w * (Y (i - 1) * Z (i - 2))) :=
    Fintype.sum_equiv (Equiv.addRight (2 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.coe_addRight]; ring_nf)
  have e5 : ∑ i, Z i * (w * (X (i - 1) * Y (i + 1)))
      = ∑ i, X i * (w * (Y (i + 2) * Z (i + 1))) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.subRight_apply]; ring_nf)
  have e6 : ∑ i, Z i * (w * (X (i - 1) * Y (i - 2)))
      = ∑ i, X i * (w * (Y (i - 1) * Z (i + 1))) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod n)) _ _ (fun i => by
      simp only [Equiv.subRight_apply]; ring_nf)
  rw [e1, e2, e3, e4, e5, e6]
  ring

end LwPencil

section GTFPencil

variable {R : Type*} [CommRing R]

/-- The split matrix `diag(X) - (c_i X_{i+α})_{(i, i+β)}` of the multiplication
`x ∘ y = x y - c σ^α(x) σ^β(y)`, with `c_i = σ^i(c)`. -/
def gtfM (c : ZMod n → R) (α β : ZMod n) (X : ZMod n → R) : Matrix (ZMod n) (ZMod n) R :=
  Matrix.diagonal X - shiftM β (fun i => c i * X (i + α))

lemma gtfM_mulVec (c : ZMod n → R) (α β : ZMod n) (X Y : ZMod n → R) (i : ZMod n) :
    (gtfM c α β X).mulVec Y i = X i * Y i - c i * X (i + α) * Y (i + β) := by
  simp only [gtfM, Matrix.sub_mulVec, Pi.sub_apply, shiftM_mulVec, Matrix.mulVec_diagonal]

lemma gtfM_apply_eq_sum (c : ZMod n → R) (α β : ZMod n) (X : ZMod n → R) (i j : ZMod n) :
    gtfM c α β X i j = ∑ k, X k * gtfM c α β (Pi.single k 1) i j := by
  simp only [gtfM, Matrix.sub_apply, Matrix.diagonal_apply, shiftM_apply]
  split_ifs <;> simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_comm]

variable {F : Type*} [Field F]

/-- The coefficient matrices of the pencil `G(X)`. -/
noncomputable def gtfP (c : ZMod n → F) (α β : ZMod n) (k : ZMod n) :
    Matrix (ZMod n) (ZMod n) F :=
  gtfM c α β (Pi.single k 1)

lemma gtfM_eq_pen {S : Type*} [CommRing S] [Algebra F S] (c : ZMod n → F) (α β : ZMod n)
    (Y : ZMod n → S) :
    gtfM (fun i => algebraMap F S (c i)) α β Y = pen (gtfP c α β) Y := by
  ext i j
  rw [pen_apply, gtfM_apply_eq_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  simp only [gtfP, gtfM, Matrix.sub_apply, Matrix.diagonal_apply, shiftM_apply]
  split_ifs <;> simp [Pi.single_apply, apply_ite (algebraMap F S)]

lemma pen_gtfP_self (c : ZMod n → F) (α β : ZMod n) (X : ZMod n → F) :
    pen (gtfP c α β) X = gtfM c α β X := by
  rw [← gtfM_eq_pen]; rfl

/-- The determinant of `G(X)` at a point with nonzero coordinates. -/
lemma det_gtfM_of_ne_zero {E : Type*} [Field E] (c : ZMod n → E) (α : ZMod n) {β : ZMod n}
    (hβ : IsUnit β) (hβ0 : β ≠ 0) (hodd : Odd n) (X : ZMod n → E) (hX : ∀ i, X i ≠ 0) :
    (gtfM c α β X).det = (1 - ∏ i, c i) * ∏ i, X i := by
  have hfac : gtfM c α β X = Matrix.diagonal X *
      ((1 : E) • (1 : Matrix (ZMod n) (ZMod n) E)
        + shiftM β (fun i => -(c i * X (i + α)) / X i)) := by
    ext i j
    simp only [gtfM, Matrix.sub_apply, Matrix.diagonal_apply, shiftM_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, one_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      split_ifs <;> field_simp [hX i] <;> ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, det_smul_one_add_shiftM 1 hβ hβ0 hodd, one_pow]
  have hprod : ∏ i, (-(c i * X (i + α)) / X i) = -∏ i, c i := by
    rw [Finset.prod_div_distrib]
    simp only [neg_mul_eq_neg_mul, Finset.prod_mul_distrib]
    rw [Finset.prod_neg, prod_shift α X, Finset.card_univ, ZMod.card, hodd.neg_one_pow]
    field_simp [Finset.prod_ne_zero_iff.mpr (fun i _ => hX i)]
  rw [hprod]
  ring

/-- **The left determinant of `G(X)` at every polynomial point.** -/
theorem det_pen_gtfP (c : ZMod n → F) (α : ZMod n) {β : ZMod n} (hβ : IsUnit β) (hβ0 : β ≠ 0)
    (hodd : Odd n) (Y : ZMod n → MvPolynomial (ZMod n) F) :
    (pen (gtfP c α β) Y).det = MvPolynomial.C (1 - ∏ i, c i) * ∏ i, Y i := by
  let A := MvPolynomial (ZMod n) F
  let f := algebraMap A (FractionRing A)
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective A (FractionRing A)
  have hXpoly : (pen (gtfP c α β) (fun i => (MvPolynomial.X i : A))).det
      = MvPolynomial.C (1 - ∏ i, c i) * ∏ i, (MvPolynomial.X i : A) := by
    apply hinj
    rw [← gtfM_eq_pen, RingHom.map_det]
    have hmap : f.mapMatrix (gtfM (fun i => algebraMap F A (c i)) α β
        (fun i => MvPolynomial.X i))
        = gtfM (fun i => f (algebraMap F A (c i))) α β (fun i => f (MvPolynomial.X i)) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, gtfM, Matrix.sub_apply,
        Matrix.diagonal_apply, shiftM_apply]
      split_ifs <;> simp
    rw [hmap]
    have hX : ∀ i : ZMod n, f (MvPolynomial.X (R := F) i) ≠ 0 := fun i h =>
      MvPolynomial.X_ne_zero i (hinj (by simpa using h))
    rw [det_gtfM_of_ne_zero _ α hβ hβ0 hodd _ hX]
    simp only [map_mul, map_prod, map_sub, map_one]
    rfl
  have := congrArg (MvPolynomial.aeval (R := F) Y) hXpoly
  rw [AlgHom.map_det] at this
  have hmap : (MvPolynomial.aeval Y).mapMatrix (pen (gtfP c α β)
      (fun i => (MvPolynomial.X i : A))) = pen (gtfP c α β) Y := by
    rw [← gtfM_eq_pen, ← gtfM_eq_pen]
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, gtfM, Matrix.sub_apply,
      Matrix.diagonal_apply, shiftM_apply]
    split_ifs <;> simp
  rw [hmap] at this
  rw [this]
  simp [map_prod]

/-- At a point with a single nonzero coordinate, `G` has rank at most two. -/
theorem rank_gtfM_single_le (c : ZMod n → F) (α β m : ZMod n) (μ : F) :
    (gtfM c α β (Pi.single m μ)).rank ≤ 2 := by
  classical
  set G := gtfM c α β (Pi.single m μ)
  have hrows : ∀ i, i ≠ m → i ≠ m - α → G i = 0 := by
    intro i h1 h2
    funext j
    simp only [G, gtfM, Matrix.sub_apply, Matrix.diagonal_apply, shiftM_apply, Pi.zero_apply]
    have h3 : i + α ≠ m := fun h => h2 (by rw [← h]; ring)
    simp [h1, h3]
  rw [Matrix.rank_eq_finrank_span_row]
  have hsub : Set.range G ⊆ ({G m, G (m - α), 0} : Set (ZMod n → F)) := by
    rintro _ ⟨i, rfl⟩
    by_cases h1 : i = m
    · subst h1; simp
    · by_cases h2 : i = m - α
      · subst h2; simp
      · simp [hrows i h1 h2]
  have hspan : Submodule.span F (Set.range G) ≤ Submodule.span F {G m, G (m - α)} := by
    refine Submodule.span_le.mpr (fun v hv => ?_)
    rcases hsub hv with h | h | h
    · exact Submodule.subset_span (by simp [h])
    · exact Submodule.subset_span (by simp [h])
    · rw [Set.mem_singleton_iff.mp h]; exact Submodule.zero_mem _
  calc Module.finrank F (Submodule.span F (Set.range G))
      ≤ Module.finrank F (Submodule.span F ({G m, G (m - α)} : Set (ZMod n → F))) :=
        Submodule.finrank_mono hspan
    _ ≤ ({G m, G (m - α)} : Finset (ZMod n → F)).card := by
        have := finrank_span_finset_le_card (R := F) ({G m, G (m - α)} : Finset (ZMod n → F))
        simpa using this
    _ ≤ 2 := Finset.card_le_two

end GTFPencil

end Semifields
