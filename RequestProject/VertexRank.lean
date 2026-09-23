import RequestProject.FamilyMatrix
import RequestProject.Nuclei

/-!
# The rank of the split matrix at a coordinate point

By `thm:division` the split left determinant of the family is
`det L_w(X) = λ_n(w) ∏ X_i`, a product of `n` independent linear forms, so its determinant
vertices are the coordinate points.  The paper computes the rank of the split matrix there:
`L_w(e_0)` has exactly four nonzero rows, carrying a `4 × 4` matrix of determinant `w ^ 2`,
so

`rank L_w(e_0) = 4`.

This is the computation behind the determinant profile `eq:new-central-profile` of the new
family.  The main result of this file is `rank_LwM_coordPt`.
-/

namespace Semifields

open scoped BigOperators
open Matrix

section CoordinatePoint

variable {n : ℕ} [NeZero n] {E : Type*} [Field E]

/-- The coordinate point `e_0` of the split coordinates. -/
noncomputable def coordPt (n : ℕ) [NeZero n] (E : Type*) [Field E] : ZMod n → E :=
  Pi.single 0 1

omit [NeZero n] in
/-- The four index distinctness facts used throughout: for `n ≥ 5` the elements
`-2, -1, 1, 2` of `ZMod n` are pairwise distinct. -/
lemma idx_ne (hn5 : 5 ≤ n) :
    (1 : ZMod n) ≠ -1 ∧ (1 : ZMod n) ≠ -2 ∧ (1 : ZMod n) ≠ 2 ∧
      (2 : ZMod n) ≠ -1 ∧ (2 : ZMod n) ≠ -2 ∧ (-1 : ZMod n) ≠ -2 := by
  obtain ⟨h1, h2, h3, h4⟩ := zmod_small_facts (n := n) hn5
  exact ⟨fun h => h2 (by linear_combination h), fun h => h3 (by linear_combination h),
    fun h => h1 (by linear_combination -h), fun h => h3 (by linear_combination h),
    fun h => h4 (by linear_combination h), fun h => h1 (by linear_combination h)⟩

/-- The rows of `L_w(e_0)`: only the rows `-1, 2, -2, 1` are nonzero. -/
lemma LwM_coordPt_mulVec (w : E) (Y : ZMod n → E) (i : ZMod n) :
    (LwM w (coordPt n E)).mulVec Y i
      = (if i = -1 then Y (i + 2) + Y (i - 1) else 0) + (if i = 2 then Y (i - 1) else 0)
        + w * ((if i = -2 then Y (i + 1) else 0)
            + (if i = 1 then Y (i + 1) + Y (i - 2) else 0)) := by
  rw [LwM_mulVec]
  have hA : coordPt n E (i + 1) = if i = -1 then 1 else 0 := by
    simp [coordPt, Pi.single_apply, add_eq_zero_iff_eq_neg]
  have hB : coordPt n E (i + 2) = if i = -2 then 1 else 0 := by
    simp [coordPt, Pi.single_apply, add_eq_zero_iff_eq_neg]
  have hC : coordPt n E (i - 1) = if i = 1 then 1 else 0 := by
    simp [coordPt, Pi.single_apply, sub_eq_zero]
  have hD : coordPt n E (i - 2) = if i = 2 then 1 else 0 := by
    simp [coordPt, Pi.single_apply, sub_eq_zero]
  rw [hA, hB, hC, hD]
  split_ifs <;> ring

lemma LwM_coordPt_row_eq_zero (w : E) (Y : ZMod n → E) {i : ZMod n}
    (h1 : i ≠ -1) (h2 : i ≠ 2) (h3 : i ≠ -2) (h4 : i ≠ 1) :
    (LwM w (coordPt n E)).mulVec Y i = 0 := by
  rw [LwM_coordPt_mulVec, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring

/-- The four nonzero columns of `L_w(e_0)`. -/
lemma LwM_coordPt_cols (hn5 : 5 ≤ n) (w : E) :
    (LwM w (coordPt n E)).mulVec (Pi.single (-2) 1) = (Pi.single (-1) 1 : ZMod n → E)
    ∧ (LwM w (coordPt n E)).mulVec (Pi.single 2 1) = w • (Pi.single 1 1 : ZMod n → E)
    ∧ (LwM w (coordPt n E)).mulVec (Pi.single 1 1)
        = (Pi.single (-1) 1 : ZMod n → E) + Pi.single 2 1
    ∧ (LwM w (coordPt n E)).mulVec (Pi.single (-1) 1)
        = w • ((Pi.single (-2) 1 : ZMod n → E) + Pi.single 1 1) := by
  obtain ⟨n1m1, n1m2, n12, n2m1, n2m2, nm1m2⟩ := idx_ne (n := n) hn5
  have n1m1' : (-1 : ZMod n) ≠ 1 := n1m1.symm
  have n1m2' : (-2 : ZMod n) ≠ 1 := n1m2.symm
  have n12' : (2 : ZMod n) ≠ 1 := n12.symm
  have n2m1' : (-1 : ZMod n) ≠ 2 := n2m1.symm
  have n2m2' : (-2 : ZMod n) ≠ 2 := n2m2.symm
  have nm1m2' : (-2 : ZMod n) ≠ -1 := nm1m2.symm
  have e1 : (-1 : ZMod n) + 2 = 1 := by ring
  have e2 : (-1 : ZMod n) - 1 = -2 := by ring
  have e3 : (2 : ZMod n) - 1 = 1 := by ring
  have e4 : (-2 : ZMod n) + 1 = -1 := by ring
  have e5 : (1 : ZMod n) + 1 = 2 := by ring
  have e6 : (1 : ZMod n) - 2 = -1 := by ring
  clear hn5
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;>
    simp only [LwM_coordPt_mulVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals rcases eq_or_ne i (-1) with rfl | hi
  all_goals try rcases eq_or_ne i 2 with rfl | hj
  all_goals try rcases eq_or_ne i (-2) with rfl | hk
  all_goals try rcases eq_or_ne i 1 with rfl | hl
  all_goals simp [*]

/-- The four vertex indices `-2, -1, 1, 2`. -/
def vtxIdx (n : ℕ) [NeZero n] : Fin 4 → ZMod n := ![-2, -1, 1, 2]

lemma vtxIdx_injective (hn5 : 5 ≤ n) : Function.Injective (vtxIdx n) := by
  obtain ⟨n1m1, n1m2, n12, n2m1, n2m2, nm1m2⟩ := idx_ne (n := n) hn5
  have n1m1' : (-1 : ZMod n) ≠ 1 := n1m1.symm
  have n1m2' : (-2 : ZMod n) ≠ 1 := n1m2.symm
  have n12' : (2 : ZMod n) ≠ 1 := n12.symm
  have n2m1' : (-1 : ZMod n) ≠ 2 := n2m1.symm
  have n2m2' : (-2 : ZMod n) ≠ 2 := n2m2.symm
  have nm1m2' : (-2 : ZMod n) ≠ -1 := nm1m2.symm
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [vtxIdx]

/-- The standard basis vectors at the four vertex indices are linearly independent. -/
lemma linearIndependent_vtx (hn5 : 5 ≤ n) :
    LinearIndependent E (fun k : Fin 4 => (Pi.single (vtxIdx n k) 1 : ZMod n → E)) := by
  have hb : (fun i : ZMod n => (Pi.single i 1 : ZMod n → E)) = ⇑(Pi.basisFun E (ZMod n)) := by
    funext i
    rw [Pi.basisFun_apply]
  have h := (Pi.basisFun E (ZMod n)).linearIndependent
  rw [← hb] at h
  exact h.comp (vtxIdx n) (vtxIdx_injective hn5)

/-- The column space of `L_w(e_0)` is spanned by the four standard basis vectors at the
indices `-2, -1, 1, 2`. -/
lemma range_LwM_coordPt (hn5 : 5 ≤ n) {w : E} (hw : w ≠ 0) :
    LinearMap.range (LwM w (coordPt n E)).mulVecLin
      = Submodule.span E
        (Set.range (fun k : Fin 4 => (Pi.single (vtxIdx n k) 1 : ZMod n → E))) := by
  classical
  obtain ⟨c1, c2, c3, c4⟩ := LwM_coordPt_cols hn5 w
  obtain ⟨n1m1, n1m2, n12, n2m1, n2m2, nm1m2⟩ := idx_ne (n := n) hn5
  have n1m1' : (-1 : ZMod n) ≠ 1 := n1m1.symm
  have n1m2' : (-2 : ZMod n) ≠ 1 := n1m2.symm
  have n12' : (2 : ZMod n) ≠ 1 := n12.symm
  have n2m1' : (-1 : ZMod n) ≠ 2 := n2m1.symm
  have n2m2' : (-2 : ZMod n) ≠ 2 := n2m2.symm
  have nm1m2' : (-2 : ZMod n) ≠ -1 := nm1m2.symm
  apply le_antisymm
  · rintro _ ⟨Y, rfl⟩
    have hval : (LwM w (coordPt n E)).mulVecLin Y
        = ∑ k : Fin 4, ((LwM w (coordPt n E)).mulVec Y) (vtxIdx n k)
            • (Pi.single (vtxIdx n k) 1 : ZMod n → E) := by
      funext j
      rw [Matrix.mulVecLin_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Fin.sum_univ_four, vtxIdx, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rcases eq_or_ne j (-1) with rfl | hi
      · simp [*]
      · rcases eq_or_ne j 2 with rfl | hj
        · simp [*]
        · rcases eq_or_ne j (-2) with rfl | hk
          · simp [*]
          · rcases eq_or_ne j 1 with rfl | hl
            · simp [*]
            · rw [LwM_coordPt_row_eq_zero w Y hi hj hk hl]
              simp [*]
    rw [hval]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨k, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hm1 : (Pi.single (-1) 1 : ZMod n → E) ∈
        LinearMap.range (LwM w (coordPt n E)).mulVecLin :=
      ⟨(Pi.single (-2) 1 : ZMod n → E), by rw [Matrix.mulVecLin_apply]; exact c1⟩
    have h1 : (Pi.single 1 1 : ZMod n → E) ∈
        LinearMap.range (LwM w (coordPt n E)).mulVecLin := by
      refine ⟨w⁻¹ • (Pi.single 2 1 : ZMod n → E), ?_⟩
      rw [map_smul, Matrix.mulVecLin_apply, c2, smul_smul, inv_mul_cancel₀ hw, one_smul]
    have hm2 : (Pi.single (-2) 1 : ZMod n → E) ∈
        LinearMap.range (LwM w (coordPt n E)).mulVecLin := by
      refine ⟨w⁻¹ • ((Pi.single (-1) 1 : ZMod n → E) - (Pi.single 2 1 : ZMod n → E)), ?_⟩
      rw [map_smul, map_sub, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, c2, c4, smul_add,
        add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hw, one_smul]
    have h2 : (Pi.single 2 1 : ZMod n → E) ∈
        LinearMap.range (LwM w (coordPt n E)).mulVecLin := by
      refine ⟨(Pi.single 1 1 : ZMod n → E) - (Pi.single (-2) 1 : ZMod n → E), ?_⟩
      rw [map_sub, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, c1, c3]
      abel
    fin_cases k <;> simpa [vtxIdx] using (by assumption : _)

/-- **The rank computation `eq:rank-four`.**  At a coordinate point of the split
coordinates, the split multiplication matrix of the family has rank four. -/
theorem rank_LwM_coordPt (hn5 : 5 ≤ n) {w : E} (hw : w ≠ 0) :
    (LwM w (coordPt n E)).rank = 4 := by
  rw [Matrix.rank, range_LwM_coordPt hn5 hw,
    finrank_span_eq_card (linearIndependent_vtx (E := E) hn5), Fintype.card_fin]

end CoordinatePoint

end Semifields
