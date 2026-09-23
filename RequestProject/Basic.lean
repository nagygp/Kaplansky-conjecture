import Mathlib

/-!
# Presemifields, isotopy, spread sets and idealisers

This file sets up the basic notions of the paper (Section `sec:preliminaries`).

* `IsPresemifield` : a `K`-bilinear multiplication without zero divisors
  (Definition `def:semifield`).
* `Isotopic` : existence of an isotopism, i.e. a triple of additive bijections `(A, B, C)`
  with `(A x) ∘ (B y) = C (x * y)` (Definition `def:isotopy`).
* `IsotopicLin` : `K`-linear isotopy.
* `spreadSet`, `dualSpreadSet` : the sets `{R_y}` and `{L_x}` of right and left
  multiplication maps (`eq:spreadset`).
* `leftIdealiser`, `rightIdealiser` : the idealisers of a spread set (`eq:idealisers`).
* `leftNucleus`, `middleNucleus`, `rightNucleus`, `semifieldCentre` : the nuclei and the
  centre of a semifield.
-/

namespace Semifields

section Presemifield

variable (K : Type*) [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A `K`-bilinear multiplication `mul` on `V` is a *presemifield multiplication* if it has
no zero divisors and `V` is nontrivial. -/
structure IsPresemifield (mul : V →ₗ[K] V →ₗ[K] V) : Prop where
  /-- The multiplication has no zero divisors. -/
  eq_zero_or_eq_zero : ∀ x y : V, mul x y = 0 → x = 0 ∨ y = 0
  /-- The underlying space is nontrivial. -/
  exists_ne_zero : ∃ x : V, x ≠ 0

variable {K}

/-- Two multiplications are *isotopic* if there is a triple of additive bijections
`(A, B, C)` with `(A x) ∘ (B y) = C (x * y)`. -/
def Isotopic (mulP : V → V → V) (mulQ : W → W → W) : Prop :=
  ∃ A B C : V ≃+ W, ∀ x y : V, mulQ (A x) (B y) = C (mulP x y)

/-- `K`-linear isotopy: the three bijections are `K`-linear. -/
def IsotopicLin (K : Type*) [Field K] [Module K V] [Module K W]
    (mulP : V → V → V) (mulQ : W → W → W) : Prop :=
  ∃ A B C : V ≃ₗ[K] W, ∀ x y : V, mulQ (A x) (B y) = C (mulP x y)

lemma Isotopic.refl (mulP : V → V → V) : Isotopic mulP mulP :=
  ⟨AddEquiv.refl V, AddEquiv.refl V, AddEquiv.refl V, fun _ _ => rfl⟩

lemma IsotopicLin.toIsotopic {mulP : V → V → V} {mulQ : W → W → W}
    (h : IsotopicLin K mulP mulQ) : Isotopic mulP mulQ := by
  obtain ⟨A, B, C, hABC⟩ := h
  exact ⟨A.toAddEquiv, B.toAddEquiv, C.toAddEquiv, hABC⟩

end Presemifield

section SpreadSet

variable {V : Type*} [AddCommGroup V]

/-- The spread set `{R_y : y ∈ V}` of a multiplication, where `R_y x = x * y`; the maps are
regarded as additive endomorphisms (`eq:spreadset`). -/
def spreadSet (mul : V → V → V) (hadd : ∀ y, ∀ x₁ x₂, mul (x₁ + x₂) y = mul x₁ y + mul x₂ y) :
    Set (V →+ V) :=
  Set.range fun y : V => AddMonoidHom.mk' (fun x => mul x y) (fun x₁ x₂ => hadd y x₁ x₂)

/-- The spread set of the dual (opposite) multiplication, `{L_x : x ∈ V}` with `L_x y = x * y`. -/
def dualSpreadSet (mul : V → V → V) (hadd : ∀ x, ∀ y₁ y₂, mul x (y₁ + y₂) = mul x y₁ + mul x y₂) :
    Set (V →+ V) :=
  Set.range fun x : V => AddMonoidHom.mk' (fun y => mul x y) (fun y₁ y₂ => hadd x y₁ y₂)

/-- The left idealiser `{T : T 𝒞 ⊆ 𝒞}` of a set of additive endomorphisms
(`eq:idealisers`). -/
def leftIdealiser (C : Set (V →+ V)) : Set (V →+ V) :=
  {T | ∀ U ∈ C, T.comp U ∈ C}

/-- The right idealiser `{T : 𝒞 T ⊆ 𝒞}` of a set of additive endomorphisms
(`eq:idealisers`). -/
def rightIdealiser (C : Set (V →+ V)) : Set (V →+ V) :=
  {T | ∀ U ∈ C, U.comp T ∈ C}

end SpreadSet

section Nuclei

variable {S : Type*} [AddCommGroup S]

/-- The left nucleus of a multiplication. -/
def leftNucleus (mul : S → S → S) : Set S :=
  {a | ∀ x y, mul a (mul x y) = mul (mul a x) y}

/-- The middle nucleus of a multiplication. -/
def middleNucleus (mul : S → S → S) : Set S :=
  {a | ∀ x y, mul x (mul a y) = mul (mul x a) y}

/-- The right nucleus of a multiplication. -/
def rightNucleus (mul : S → S → S) : Set S :=
  {a | ∀ x y, mul x (mul y a) = mul (mul x y) a}

/-- The centre of a multiplication. -/
def semifieldCentre (mul : S → S → S) : Set S :=
  {a | a ∈ leftNucleus mul ∧ a ∈ middleNucleus mul ∧ a ∈ rightNucleus mul ∧
        ∀ x, mul a x = mul x a}

end Nuclei

end Semifields
