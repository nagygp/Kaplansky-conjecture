import RequestProject.Basic

/-!
# Semifields, Kaplansky's trick and nuclei via idealisers

* `IsSemifield` : a biadditive multiplication without zero divisors and with a two-sided
  identity (Definition `def:semifield`).
* `Isotopic.symm`, `Isotopic.trans` : isotopy is an equivalence relation.
* `kapMul` and `isSemifield_kapMul`, `isotopic_kapMul` : Kaplansky's trick
  (Lemma `lem:kaplansky`), turning a presemifield into an isotopic semifield.
* `card_leftIdealiser_eq`, `card_rightIdealiser_eq` : the idealisers of the spread sets of
  isotopic multiplications are conjugate, hence have the same cardinality.
* `card_rightNucleus`, `card_middleNucleus`, `card_leftNucleus` : for a semifield the three
  nuclei are in bijection with the idealisers of its spread sets
  (Proposition `prop:spread-nuclei`).
-/

namespace Semifields

section Isotopy

variable {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]

/-- A multiplication on an additive group is a *semifield multiplication* if it is biadditive,
has no zero divisors, has a two-sided identity, and the group is nontrivial. -/
structure IsSemifield (mul : V → V → V) : Prop where
  add_left : ∀ x₁ x₂ y, mul (x₁ + x₂) y = mul x₁ y + mul x₂ y
  add_right : ∀ x y₁ y₂, mul x (y₁ + y₂) = mul x y₁ + mul x y₂
  eq_zero_or_eq_zero : ∀ x y, mul x y = 0 → x = 0 ∨ y = 0
  exists_one : ∃ e, ∀ x, mul e x = x ∧ mul x e = x
  exists_ne_zero : ∃ x : V, x ≠ 0

lemma Isotopic.symm {mulP : V → V → V} {mulQ : W → W → W} (h : Isotopic mulP mulQ) :
    Isotopic mulQ mulP := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨A.symm, B.symm, C.symm, fun x y => ?_⟩
  have := h (A.symm x) (B.symm y)
  simp only [AddEquiv.apply_symm_apply] at this
  rw [this, AddEquiv.symm_apply_apply]

lemma Isotopic.trans {mulP : V → V → V} {mulQ : W → W → W} {mulR : U → U → U}
    (h₁ : Isotopic mulP mulQ) (h₂ : Isotopic mulQ mulR) : Isotopic mulP mulR := by
  obtain ⟨A₁, B₁, C₁, h₁⟩ := h₁
  obtain ⟨A₂, B₂, C₂, h₂⟩ := h₂
  refine ⟨A₁.trans A₂, B₁.trans B₂, C₁.trans C₂, fun x y => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [h₂, h₁]

end Isotopy

section Kaplansky

variable {V : Type*} [AddCommGroup V]

/-- **Kaplansky's trick** (`lem:kaplansky`): `x ∘ y = R_a⁻¹(x) * L_a⁻¹(y)`, where
`R_a x = x * a` and `L_a y = a * y` are given as additive bijections. -/
def kapMul (mul : V → V → V) (Ra La : V ≃+ V) : V → V → V :=
  fun x y => mul (Ra.symm x) (La.symm y)

variable {mul : V → V → V} {a : V} {Ra La : V ≃+ V}

lemma isotopic_kapMul : Isotopic mul (kapMul mul Ra La) := by
  refine ⟨Ra, La, AddEquiv.refl V, fun x y => ?_⟩
  simp [kapMul]

lemma isSemifield_kapMul (hadd₁ : ∀ x₁ x₂ y, mul (x₁ + x₂) y = mul x₁ y + mul x₂ y)
    (hadd₂ : ∀ x y₁ y₂, mul x (y₁ + y₂) = mul x y₁ + mul x y₂)
    (hzero : ∀ x y, mul x y = 0 → x = 0 ∨ y = 0) (ha : a ≠ 0)
    (hRa : ∀ x, Ra x = mul x a) (hLa : ∀ y, La y = mul a y) :
    IsSemifield (kapMul mul Ra La) where
  add_left x₁ x₂ y := by simp only [kapMul, map_add, hadd₁]
  add_right x y₁ y₂ := by simp only [kapMul, map_add, hadd₂]
  eq_zero_or_eq_zero x y h := by
    rcases hzero _ _ h with h' | h'
    · left; simpa using congrArg Ra h'
    · right; simpa using congrArg La h'
  exists_one := by
    refine ⟨mul a a, fun x => ⟨?_, ?_⟩⟩
    · simp only [kapMul]
      have : Ra.symm (mul a a) = a := by
        rw [AddEquiv.symm_apply_eq, hRa]
      rw [this, ← hLa, AddEquiv.apply_symm_apply]
    · simp only [kapMul]
      have : La.symm (mul a a) = a := by
        rw [AddEquiv.symm_apply_eq, hLa]
      rw [this, ← hRa, AddEquiv.apply_symm_apply]
  exists_ne_zero := ⟨a, ha⟩

end Kaplansky

section Idealisers

variable {V : Type*} [AddCommGroup V]

lemma mem_spreadSet_iff {mul : V → V → V} {hadd} {U : V →+ V} :
    U ∈ spreadSet mul hadd ↔ ∃ y, ∀ x, U x = mul x y := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun x => rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, AddMonoidHom.ext fun x => (hy x).symm⟩

lemma mem_leftIdealiser_spreadSet_iff {mul : V → V → V} {hadd} {T : V →+ V} :
    T ∈ leftIdealiser (spreadSet mul hadd) ↔ ∀ y, ∃ z, ∀ x, T (mul x y) = mul x z := by
  constructor
  · intro hT y
    have := hT _ ((mem_spreadSet_iff (U := AddMonoidHom.mk' (fun x => mul x y) (hadd y))).mpr
      ⟨y, fun x => rfl⟩)
    obtain ⟨z, hz⟩ := mem_spreadSet_iff.mp this
    exact ⟨z, hz⟩
  · intro hT U hU
    obtain ⟨y, hy⟩ := mem_spreadSet_iff.mp hU
    obtain ⟨z, hz⟩ := hT y
    exact mem_spreadSet_iff.mpr ⟨z, fun x => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, hy, hz]⟩

lemma mem_rightIdealiser_spreadSet_iff {mul : V → V → V} {hadd} {T : V →+ V} :
    T ∈ rightIdealiser (spreadSet mul hadd) ↔ ∀ y, ∃ z, ∀ x, mul (T x) y = mul x z := by
  constructor
  · intro hT y
    have := hT _ ((mem_spreadSet_iff (U := AddMonoidHom.mk' (fun x => mul x y) (hadd y))).mpr
      ⟨y, fun x => rfl⟩)
    obtain ⟨z, hz⟩ := mem_spreadSet_iff.mp this
    exact ⟨z, hz⟩
  · intro hT U hU
    obtain ⟨y, hy⟩ := mem_spreadSet_iff.mp hU
    obtain ⟨z, hz⟩ := hT y
    exact mem_spreadSet_iff.mpr ⟨z, fun x => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, hy, hz]⟩

variable {mulP mulS : V → V → V}
  {haddP : ∀ y, ∀ x₁ x₂, mulP (x₁ + x₂) y = mulP x₁ y + mulP x₂ y}
  {haddS : ∀ y, ∀ x₁ x₂, mulS (x₁ + x₂) y = mulS x₁ y + mulS x₂ y}

/-- Conjugation by the output map of an isotopism carries left idealisers. -/
lemma conj_mem_leftIdealiser {A B C : V ≃+ V} (h : ∀ x y, mulS (A x) (B y) = C (mulP x y))
    {T : V →+ V} (hT : T ∈ leftIdealiser (spreadSet mulS haddS)) :
    C.symm.toAddMonoidHom.comp (T.comp C.toAddMonoidHom)
      ∈ leftIdealiser (spreadSet mulP haddP) := by
  rw [mem_leftIdealiser_spreadSet_iff] at hT ⊢
  intro y
  obtain ⟨z, hz⟩ := hT (B y)
  refine ⟨B.symm z, fun x => ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← h, hz, ← AddEquiv.apply_symm_apply B z, h, AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply]

/-- Conjugation by the first map of an isotopism carries right idealisers. -/
lemma conj_mem_rightIdealiser {A B C : V ≃+ V} (h : ∀ x y, mulS (A x) (B y) = C (mulP x y))
    {T : V →+ V} (hT : T ∈ rightIdealiser (spreadSet mulS haddS)) :
    A.symm.toAddMonoidHom.comp (T.comp A.toAddMonoidHom)
      ∈ rightIdealiser (spreadSet mulP haddP) := by
  rw [mem_rightIdealiser_spreadSet_iff] at hT ⊢
  intro y
  obtain ⟨z, hz⟩ := hT (B y)
  refine ⟨B.symm z, fun x => ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  apply C.injective
  rw [← h, AddEquiv.apply_symm_apply, hz, ← h, AddEquiv.apply_symm_apply]

lemma inv_isotopism {A B C : V ≃+ V} (h : ∀ x y, mulS (A x) (B y) = C (mulP x y)) :
    ∀ x y, mulP (A.symm x) (B.symm y) = C.symm (mulS x y) := by
  intro x y
  have := h (A.symm x) (B.symm y)
  simp only [AddEquiv.apply_symm_apply] at this
  rw [this, AddEquiv.symm_apply_apply]

/-- The left idealisers of the spread sets of isotopic multiplications have the same
cardinality. -/
theorem card_leftIdealiser_eq {A B C : V ≃+ V} (h : ∀ x y, mulS (A x) (B y) = C (mulP x y)) :
    Nat.card (leftIdealiser (spreadSet mulS haddS))
      = Nat.card (leftIdealiser (spreadSet mulP haddP)) := by
  refine Nat.card_congr
    { toFun := fun T => ⟨_, conj_mem_leftIdealiser (haddP := haddP) h T.2⟩
      invFun := fun T => ⟨_, conj_mem_leftIdealiser (haddP := haddS) (inv_isotopism h) T.2⟩
      left_inv := fun T => ?_
      right_inv := fun T => ?_ }
  · ext x; simp
  · ext x; simp

/-- The right idealisers of the spread sets of isotopic multiplications have the same
cardinality. -/
theorem card_rightIdealiser_eq {A B C : V ≃+ V} (h : ∀ x y, mulS (A x) (B y) = C (mulP x y)) :
    Nat.card (rightIdealiser (spreadSet mulS haddS))
      = Nat.card (rightIdealiser (spreadSet mulP haddP)) := by
  refine Nat.card_congr
    { toFun := fun T => ⟨_, conj_mem_rightIdealiser (haddP := haddP) h T.2⟩
      invFun := fun T => ⟨_, conj_mem_rightIdealiser (haddP := haddS) (inv_isotopism h) T.2⟩
      left_inv := fun T => ?_
      right_inv := fun T => ?_ }
  · ext x; simp
  · ext x; simp

end Idealisers

section Nuclei

variable {V : Type*} [AddCommGroup V] {S : V → V → V}
  (hadd : ∀ y, ∀ x₁ x₂, S (x₁ + x₂) y = S x₁ y + S x₂ y) {e : V} (he : ∀ x, S e x = x ∧ S x e = x)
include he

/-- The right nucleus of a semifield is in bijection with the left idealiser of its spread
set (`prop:spread-nuclei`). -/
theorem card_rightNucleus :
    Nat.card (rightNucleus S) = Nat.card (leftIdealiser (spreadSet S hadd)) := by
  let f : rightNucleus S → leftIdealiser (spreadSet S hadd) := fun c =>
    ⟨AddMonoidHom.mk' (fun x => S x c) (hadd c), by
      rw [mem_leftIdealiser_spreadSet_iff]
      intro y
      exact ⟨S y c, fun x => (c.2 x y).symm⟩⟩
  refine Nat.card_eq_of_bijective f ⟨fun c d hcd => ?_, fun T => ?_⟩
  · have := congrArg (fun T : leftIdealiser (spreadSet S hadd) => (T : V →+ V) e) hcd
    simp only [f, AddMonoidHom.mk'_apply] at this
    rw [(he c).1, (he d).1] at this
    exact Subtype.ext this
  · obtain ⟨T, hT⟩ := T
    have hT' := mem_leftIdealiser_spreadSet_iff.mp hT
    obtain ⟨c, hc⟩ := hT' e
    have hTc : ∀ x, T x = S x c := fun x => by rw [← hc, (he x).2]
    refine ⟨⟨c, fun x y => ?_⟩, Subtype.ext (AddMonoidHom.ext fun x => (hTc x).symm)⟩
    obtain ⟨z, hz⟩ := hT' y
    have hze : S y c = z := by rw [← (he y).1, ← hTc, hz, (he z).1]
    rw [← hTc (S x y), hz, hze]

/-- The middle nucleus of a semifield is in bijection with the right idealiser of its spread
set (`prop:spread-nuclei`). -/
theorem card_middleNucleus :
    Nat.card (middleNucleus S) = Nat.card (rightIdealiser (spreadSet S hadd)) := by
  let f : middleNucleus S → rightIdealiser (spreadSet S hadd) := fun c =>
    ⟨AddMonoidHom.mk' (fun x => S x c) (hadd c), by
      rw [mem_rightIdealiser_spreadSet_iff]
      intro y
      exact ⟨S c y, fun x => (c.2 x y).symm⟩⟩
  refine Nat.card_eq_of_bijective f ⟨fun c d hcd => ?_, fun T => ?_⟩
  · have := congrArg (fun T : rightIdealiser (spreadSet S hadd) => (T : V →+ V) e) hcd
    simp only [f, AddMonoidHom.mk'_apply] at this
    rw [(he c).1, (he d).1] at this
    exact Subtype.ext this
  · obtain ⟨T, hT⟩ := T
    have hT' := mem_rightIdealiser_spreadSet_iff.mp hT
    obtain ⟨c, hc⟩ := hT' e
    have hTc : ∀ x, T x = S x c := fun x => by rw [← hc, (he (T x)).2]
    refine ⟨⟨c, fun x y => ?_⟩, Subtype.ext (AddMonoidHom.ext fun x => (hTc x).symm)⟩
    obtain ⟨z, hz⟩ := hT' y
    have hze : S c y = z := by
      have := hz e
      rw [hTc, (he c).1, (he z).1] at this
      exact this
    rw [← hTc x, hz, hze]

omit hadd in
/-- The left nucleus of a semifield is in bijection with the left idealiser of its dual spread
set (`prop:spread-nuclei`). -/
theorem card_leftNucleus (hadd' : ∀ x, ∀ y₁ y₂, S x (y₁ + y₂) = S x y₁ + S x y₂) :
    Nat.card (leftNucleus S) = Nat.card (leftIdealiser (dualSpreadSet S hadd')) := by
  have hmem : ∀ T : V →+ V, T ∈ dualSpreadSet S hadd' ↔ ∃ x, ∀ y, T y = S x y := by
    intro T
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, fun y => rfl⟩
    · rintro ⟨x, hx⟩; exact ⟨x, AddMonoidHom.ext fun y => (hx y).symm⟩
  have hid : ∀ T : V →+ V, T ∈ leftIdealiser (dualSpreadSet S hadd') ↔
      ∀ x, ∃ z, ∀ y, T (S x y) = S z y := by
    intro T
    constructor
    · intro hT x
      obtain ⟨z, hz⟩ := (hmem _).mp (hT _ ((hmem (AddMonoidHom.mk' (fun y => S x y)
        (hadd' x))).mpr ⟨x, fun y => rfl⟩))
      exact ⟨z, hz⟩
    · intro hT U hU
      obtain ⟨x, hx⟩ := (hmem _).mp hU
      obtain ⟨z, hz⟩ := hT x
      exact (hmem _).mpr ⟨z, fun y => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, hx, hz]⟩
  let f : leftNucleus S → leftIdealiser (dualSpreadSet S hadd') := fun c =>
    ⟨AddMonoidHom.mk' (fun y => S c y) (hadd' c), by
      rw [hid]
      intro x
      exact ⟨S c x, fun y => c.2 x y⟩⟩
  refine Nat.card_eq_of_bijective f ⟨fun c d hcd => ?_, fun T => ?_⟩
  · have := congrArg (fun T : leftIdealiser (dualSpreadSet S hadd') => (T : V →+ V) e) hcd
    simp only [f, AddMonoidHom.mk'_apply] at this
    rw [(he c).2, (he d).2] at this
    exact Subtype.ext this
  · obtain ⟨T, hT⟩ := T
    have hT' := (hid T).mp hT
    obtain ⟨c, hc⟩ := hT' e
    have hTc : ∀ y, T y = S c y := fun y => by rw [← hc, (he y).1]
    refine ⟨⟨c, fun x y => ?_⟩, Subtype.ext (AddMonoidHom.ext fun y => (hTc y).symm)⟩
    obtain ⟨z, hz⟩ := hT' x
    have hze : S c x = z := by
      have := hz e
      rw [hTc, (he x).2, (he z).2] at this
      exact this
    rw [← hTc (S x y), hz, hze]

end Nuclei

end Semifields
