# Summary of changes for run 99e56e03-508b-44ff-99d5-b6dd72728d55
I replaced the old prime-field version of `cor:menichetti` with the one in `semifields_kaplansky_shorter.tex`, which covers any prime power `q`. `RequestProject/CorollaryMenichetti.lean` has been rewritten. The whole project builds, there is no `sorry`, and the main theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**`cor_menichetti`** (in `RequestProject/CorollaryMenichetti.lean`). Setup: `K` is a finite field of characteristic `p` with `|K| = q ≡ 1 (mod 3)`, `r ≥ 5` is prime, and `F ⊇ K` has `[F : K] = r`. The theorem proves:
- **Number of classes:** the family `𝒫_{w,s}` represents exactly `r − 1` isotopy classes if `p ≡ 1 (mod 3)`, and `(r − 1)/2` if `p ≡ 2 (mod 3)`. This is stated as the size of the set of parameters `(w, σ)` modulo isotopy of the corresponding members (`FamParam`, `famIsotopySetoid`). Here `w` is a root of `X² − X + 1` and `σ` generates `Gal(F/K)`, i.e. `σ = x ↦ x^{q^s}` with `s` a unit mod `r`.
- **Order:** `|F| = q^r`. Each member is a presemifield and is isotopic to its Kaplansky semifield.
- **Nuclei:** *every* semifield on `F` isotopic to a member has centre and all three nuclei of order `q`, not only the Kaplansky one.
- **Non-isotopy:** no member is isotopic to any finite field, or to any `x y − c·τ(x)·υ(y)` on any field, for arbitrary `c`, `τ`, `υ`. This includes all Albert generalized twisted fields.

Isotopy throughout means arbitrary additive isotopy. Handling a general `q`, where isotopisms need not be `K`-linear, required these new pieces:
- **Semilinearity lemma and Galois twist** (`Semilinear.lean`): an isotopism is semilinear, and composing it with a power of the Frobenius gives a `K`-linear isotopism. For the family, the twist only changes `w` to `w^{p^j}`.
- **Classification within the family for general `q`** (`FamilyIsotopy.lean`), using the identity `𝒫_{w⁻¹,s} ≃ 𝒫_{w,−s}`.
- **Idealiser of a generalized twisted field** (`GTFIdealiser.lean`). Where the paper cites Albert's nuclear theorem to show `τ` and `υ` fix `K`, I computed this idealiser directly, using linearized polynomials over the prime field.
- **Exclusion of generalized twisted fields for all admissible `q`** (`not_isotopic_gtf`, in `GTFGeneral.lean`).
- **Centre of an arbitrary isotope** (`NucleiIsotopes.lean`).

**Consequences** (also in `CorollaryMenichetti.lean`):
- `menichetti_threshold_false`: fix a prime `r ≥ 5`, a prime `p ≠ 3` and any bound `N`. There is an `r`-dimensional division algebra over some `𝔽_q` of characteristic `p` with `q > N`, whose centre has order `q`, and which is not isotopic to a field or to any generalized twisted field. So raising the base-field threshold does not save Menichetti's Corollary 33.
- `kaplansky_counterexample`: the case `r = 5`.

**Limitations:**
- In `menichetti_threshold_false` the examples use `q = p^e` with `e` even. That covers both residues of `p` mod 3, but for `p ≡ 1 (mod 3)` the paper allows every `e`.
- Menichetti's Proposition 30 is not stated in Lean; what is proved is that the conclusion it would imply fails.
- `MainResults.lean` is unchanged.

**Properties table:** I updated `cor_menichetti` and `kaplansky_counterexample` and added entries for `menichetti_threshold_false`, `not_isotopic_gtf` and the parameter definitions, all verified by the build. I removed the entry for the old prime-field theorem. The note on `thm:nonisotopy` now says its generalized-twisted-field half is proved for prime `n` and any `q`; that entry stays in progress because composite `n` is not covered. The table can only link to the older `semifields_kaplansky_editorial.tex`, so the source links point to the same labels there, and the comments say the statements follow the shorter version.

# Summary of changes for run 1f7c7e54-850c-4e0f-ae09-73b8acb4e1d5
I formalized and proved corollary `cor:menichetti` in `RequestProject/CorollaryMenichetti.lean`. The whole project builds. There is no `sorry` anywhere, and the main theorems depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**What is proved (`RequestProject/CorollaryMenichetti.lean`)**
- `cor_menichetti`: Let `r ≥ 5` and `p ≡ 1 (mod 3)` be primes, and let `F = GaloisField p r`, so `|F| = p^r`. Then `F` carries `r − 1` multiplications with these properties:
  - each is a semifield;
  - they are pairwise nonisotopic;
  - none is isotopic to the field `F`;
  - none is isotopic to any generalized twisted field `x·y − c·τ(x)·υ(y)`, for any `c`, `τ`, `υ`. This is stronger than excluding only the Albert generalized twisted fields;
  - the centre and the left, middle and right nuclei each have exactly `p` elements.

  Isotopy here is the general (additive) isotopy of the paper.
- `centre_threshold_false`: for each prime `r ≥ 5`, there is no bound `N` such that every semifield on `GaloisField p r` whose centre has prime order `p > N` is isotopic to a field or a generalized twisted field. This is the formal version of "no increase of the base-field threshold repairs Menichetti's Corollary 33".
- `kaplansky_counterexample`: the case `r = 5`, which gives counterexamples to Kaplansky's conjecture.

**Supporting file (`RequestProject/MenichettiFamily.lean`)**
Kaplansky's trick with `a = 1` turns each presemifield of the family into an isotopic semifield, `famSemi`. The file proves that it is a semifield and that its three nuclei and its centre all have `|K|` elements. The nuclei counts come from `thm:direct-nuclei`, through the link between nuclei and idealisers of spread sets.

**How the proof follows the paper**
- A generator of the Galois group is found, and its powers by units mod `r` give the `r − 1` members.
- Over the prime field, every additive isotopism is automatically `𝔽_p`-linear. This lets the earlier linear results apply to arbitrary isotopisms:
  - the classification of generator parameters gives pairwise nonisotopy;
  - `thm:nonisotopy` excludes fields;
  - the prime-dimension result excludes generalized twisted fields.

**Limitations**
- The infinitude of primes `p ≡ 1 (mod 3)` is taken from Mathlib (`Nat.exists_prime_gt_modEq_one`); the paper's own elementary argument for it is not formalized.
- Menichetti's Proposition 30 is not formalized as a statement. What is formalized is the failure of the conclusion it would imply.
- The new files do not use the `module` keyword, because the existing project files are not modules and cannot be imported from one.

**Properties table**
I added entries for the three results above (marked proved) and for the `IsSemifield` definition. I also updated the note on `thm:nonisotopy`: its generalized-twisted-field half is now proved for prime dimension and linear isotopisms, which covers arbitrary isotopisms over a prime base field. The general statement is still not formalized, so that entry remains in progress.

# Summary of changes for run 717876c1-86b7-4549-bec8-c7d754c21517
The project now builds completely clean: a from-scratch rebuild of all fifteen modules (`RequestProject.*`) produces no warnings, no info messages and no errors, and there are no `sorry`s, no `nolint`s and no linter `set_option` suppressions anywhere. Each diagnostic was fixed at its root rather than silenced:

- **Unused section variables.** Lemmas that did not actually need `[NeZero n]`, `[FiniteDimensional K F]` etc. now carry an explicit `omit ... in` (in `Shift.lean`, `Construction.lean`, `FamilyMatrix.lean`, `Moore.lean`, `Linearized.lean`, `Nuclei.lean`, `Idealisers.lean`, `VertexRank.lean`), so the statements no longer drag in hypotheses they do not use.
- **Unused variables.** The coefficient function `e3` in `Nuclei.lean` never used its automorphism argument `σ`, so that argument was removed from the definition and from all call sites in `Nuclei.lean` and `Idealisers.lean` (including the four `e3_at_*` evaluation lemmas). In `isPresemifield_famMul` the two unused binders were replaced by `_`.
- **Unused simp arguments.** Dropped `Matrix.one_apply` in `Shift.lean`, `famMul` in `Moore.lean` and `Finset.sum_mul` in `Nuclei.lean` from the corresponding simp sets.
- **The two `ring` info messages** in `Nuclei.lean` (in `expand_e1` and `expand_e2`) came from `ring` falling back to its normalization form; those two calls are now written as `ring_nf`, which is what actually closes the goals.

All four paper theorems in `RequestProject/MainResults.lean` are unaffected in statement and remain proved as before; the entries in the Properties table are unchanged and still reflect their true status.

# Summary of changes for run 0303d648-62c2-46f8-b79e-99b4a7788a30
Continuing the formalization of *Semifields in prime dimensions and counterexamples to Kaplansky's conjecture*, I added the two main theorems that were still missing from `RequestProject/MainResults.lean`, plus a supporting computation. The whole project builds cleanly and contains no `sorry`, no `admit` and no added axioms.

New this session:

* **`thm:invariance` (`Semifields.thm_invariance`, in `MainResults.lean`).** A new file `RequestProject/Invariance.lean` develops the determinant-profile invariants over a fixed extension field `Ω` of `K`: the component splitting field `componentField` (smallest subfield over which every absolutely irreducible factor of a determinant form is defined up to a scalar), the set `absFactorDegrees` of degrees of those factors, and `vertexRanks`, the ranks of the pencil at the determinant vertices (`IsDetVertex`), which is empty exactly in the paper's `⊥` case. The core transport results (`componentField_transport`, `absFactorDegrees_transport`, `vertexRanks_transport`) show all three are unchanged under an invertible linear substitution of the variables together with a nonzero scalar factor; combined with the pencil-isotopy identities already in the project, this yields invariance of all three constituents of the relative profile, for each of the left, right and trace determinant types. The theorem is proved for `K`-linear isotopisms — the case the paper's proof establishes first; the subsequent reduction of a general isotopism via common semilinearity, and the resulting well-definedness of the central profile, are not covered, and this is stated in the theorem's docstring and in the Properties table.

* **`thm:nonisotopy`, finite-field case (`Semifields.thm_nonisotopy_field`, in `MainResults.lean`).** No member of the family is isotopic to the field multiplication of `F`, for arbitrary (not necessarily linear) isotopisms; this uses the idealiser computation of `thm:direct-nuclei`. The remaining half of `thm:nonisotopy` — exclusion of Albert generalized twisted fields, which in the paper rests on comparing determinant profiles — is not yet formalized and is flagged as still in progress.

* **The rank computation behind the family's profile (`Semifields.rank_LwM_coordPt`, new file `RequestProject/VertexRank.lean`).** For `n ≥ 5` and any `w ≠ 0`, the split multiplication matrix `L_w(X)` evaluated at a coordinate point has rank exactly four, by identifying its four nonzero rows and its column space.

I also marked `thm:direct-nuclei` as proved in the Properties table (it was already fully proved in the project), removed a leftover scratch file that did not compile, and cleaned up the linter warnings in the files I touched. The four paper theorems now stand as: `thm:division` and `thm:direct-nuclei` proved in full, `thm:invariance` proved in the `K`-linear case, and `thm:nonisotopy` proved for finite fields.