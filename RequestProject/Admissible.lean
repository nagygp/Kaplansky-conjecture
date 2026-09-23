import RequestProject.Moore

/-!
# The admissible parameters `eq:admissible`

The paper fixes `q = p^e ≡ 1 (mod 3)`, `n ≥ 5` with `gcd (n, 6) = 1`, `K = 𝔽_q`,
`F = 𝔽_{q^n}`, a unit `s` modulo `n` and `σ (x) = x ^ (q ^ s)`, and an element `w ∈ K`
with `w ^ 2 - w + 1 = 0`.

This file collects the elementary consequences of these hypotheses that are used below:

* `three_ne_zero_of_card_mod_three` : `q ≡ 1 (mod 3)` forces the characteristic to differ
  from three;
* `exists_w_of_card_mod_three` : `q ≡ 1 (mod 3)` guarantees a root of `w ^ 2 - w + 1`;
* `mod_six_of_gcd_six` : `gcd (n, 6) = 1` means `n ≡ 1` or `n ≡ 5 (mod 6)`.

In the formalisation, "`σ` generates the cyclic Galois group of order `n`" is expressed by
the bijectivity of `i ↦ σ^i` from `ZMod n` to `Gal (F / K)`; for `F = 𝔽_{q^n}` over
`K = 𝔽_q` this is exactly the condition that `s` be a unit modulo `n`.
-/

namespace Semifields

open scoped BigOperators

/-- If the order of a finite field is `≡ 1 (mod 3)`, its characteristic is not three. -/
theorem three_ne_zero_of_card_mod_three {K : Type*} [Field K] [Fintype K]
    (hq : Fintype.card K % 3 = 1) : (3 : K) ≠ 0 := by
  intro h3
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hprime : Nat.Prime p := CharP.char_is_prime K p
  have hdvd : p ∣ 3 := by
    have : ((3 : ℕ) : K) = 0 := by push_cast; exact h3
    exact (CharP.cast_eq_zero_iff K p 3).mp this
  have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hdvd)
  obtain ⟨m, _, hcard⟩ := FiniteField.card K p
  rw [hp3] at hcard
  have : (3 : ℕ) ∣ Fintype.card K := by
    rw [hcard]
    exact dvd_pow_self 3 (by exact_mod_cast m.ne_zero)
  omega

/-- If the order of a finite field is `≡ 1 (mod 3)`, then `w ^ 2 - w + 1` has a root
(`eq:parameter`). -/
theorem exists_w_of_card_mod_three {K : Type*} [Field K] [Fintype K]
    (hq : Fintype.card K % 3 = 1) : ∃ w : K, w ^ 2 - w + 1 = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Fintype.card Kˣ = Fintype.card K - 1 := Fintype.card_units K
  have hdvd : 3 ∣ Fintype.card Kˣ := by rw [hcard]; omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := Kˣ) 3 hdvd
  refine ⟨-(u : K), ?_⟩
  have hu3 : (u : K) ^ 3 = 1 := by
    have h : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg (Units.val) h
    simpa using this
  have hune : (u : K) ≠ 1 := by
    intro h
    have hu1 : u = 1 := Units.ext h
    rw [hu1] at hu
    simp at hu
  have hfac : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by linear_combination hu3
  have h2 : (u : K) ^ 2 + (u : K) + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hune
    · exact h
  linear_combination h2

/-- `gcd (n, 6) = 1` means `n ≡ 1` or `n ≡ 5 (mod 6)`. -/
theorem mod_six_of_gcd_six {n : ℕ} (h : Nat.gcd n 6 = 1) : n % 6 = 1 ∨ n % 6 = 5 := by
  have h2 : ¬ (2 ∣ n) := by
    intro hd
    have : (2 : ℕ) ∣ Nat.gcd n 6 := Nat.dvd_gcd hd (by norm_num)
    rw [h] at this
    omega
  have h3 : ¬ (3 ∣ n) := by
    intro hd
    have : (3 : ℕ) ∣ Nat.gcd n 6 := Nat.dvd_gcd hd (by norm_num)
    rw [h] at this
    omega
  have h2' : n % 2 = 1 := by omega
  have h3' : n % 3 ≠ 0 := by omega
  omega

end Semifields
