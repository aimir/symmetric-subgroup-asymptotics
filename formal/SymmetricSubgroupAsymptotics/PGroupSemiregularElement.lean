import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A semiregular element in the original transitive p-group action

The order-p element is chosen in the faithful permutation image. Its lift
to the original group need not have order p. All conclusions about points
and cyclic orbits use the original action and the original lifted element.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime]

/-- A fixed-point-free permutation of prime order has all its cyclic
orbits of cardinality that prime. -/
theorem primeOrderPermutation_orbit_card {X : Type*} [Finite X]
    (s : Equiv.Perm X) (hs : orderOf s = p) (hfree : ∀ x, s x ≠ x)
    (x : X) : Nat.card (MulAction.orbit (Subgroup.zpowers s) x) = p := by
  classical
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite (Subgroup.zpowers s)
  letI := Fintype.ofFinite (MulAction.orbit (Subgroup.zpowers s) x)
  letI := Fintype.ofFinite (MulAction.stabilizer (Subgroup.zpowers s) x)
  have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Subgroup.zpowers s) x
  have hcyclic : Nat.card (Subgroup.zpowers s) = p := (Nat.card_zpowers s).trans hs
  have hcyclic' : Fintype.card (Subgroup.zpowers s) = p := by
    simpa only [Nat.card_eq_fintype_card] using hcyclic
  rw [hcyclic'] at hmul
  have hdvd : Fintype.card (MulAction.orbit (Subgroup.zpowers s) x) ∣ p :=
    ⟨Fintype.card (MulAction.stabilizer (Subgroup.zpowers s) x), hmul.symm⟩
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
  · have hfixed := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mpr h
    exact False.elim (hfree x (hfixed ⟨s, Subgroup.mem_zpowers s⟩))
  · simpa only [Nat.card_eq_fintype_card] using h

/-- Passing to the permutation image preserves each cyclic orbit as an
actual subset of the original point set. -/
theorem cyclicOrbit_eq_permutationImageOrbit {G X : Type*} [Group G]
    [MulAction G X] (g : G) (x : X) :
    MulAction.orbit (Subgroup.zpowers g) x =
      MulAction.orbit (Subgroup.zpowers (MulAction.toPermHom G X g)) x := by
  ext y
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp u.property
    refine ⟨⟨(MulAction.toPermHom G X g) ^ n,
      Subgroup.zpow_mem_zpowers _ n⟩, ?_⟩
    change ((MulAction.toPermHom G X g) ^ n) x = y
    rw [← map_zpow]
    change g ^ n • x = y
    simpa only [hn] using hu
  · rintro ⟨u, hu⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp u.property
    refine ⟨⟨g ^ n, Subgroup.zpow_mem_zpowers g n⟩, ?_⟩
    change g ^ n • x = y
    change (MulAction.toPermHom G X (g ^ n)) x = y
    rw [map_zpow, hn]
    exact hu

/-- Equal finite cyclic-orbit sizes give the exact number of original
cyclic orbits. No faithfulness or order assumption on the acting element
is needed for this counting step. -/
theorem cyclicOrbitCount_mul_of_orbit_card {G X : Type*} [Group G]
    [MulAction G X] [Finite X] (g : G) (n : ℕ)
    (hn : ∀ x : X, Nat.card (MulAction.orbit (Subgroup.zpowers g) x) = n) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) * n =
      Nat.card X := by
  classical
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X)
  calc
    _ = ∑ o : MulAction.orbitRel.Quotient (Subgroup.zpowers g) X,
        Nat.card (MulAction.orbit (Subgroup.zpowers g) o.out) := by
      simp [hn, Nat.card_eq_fintype_card]
    _ = Nat.card X := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers g) X).symm

/-- A nontrivial finite transitive p-group action contains an actual
element whose permutation image has order p and fixes no point. The
original action is allowed to have a nontrivial kernel. -/
theorem pGroup_exists_primeOrder_fixedPointFree_image
    {G X : Type*} [Group G] [MulAction G X] [Finite X] [Nontrivial X]
    [MulAction.IsPretransitive G X] (hG : IsPGroup p G) :
    ∃ g : G, orderOf (MulAction.toPermHom G X g) = p ∧ ∀ x : X, g • x ≠ x := by
  classical
  let φ := MulAction.toPermHom G X
  let P := φ.range
  letI : MulAction.IsPretransitive P X := ⟨fun x y => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨φ.rangeRestrict g, hg⟩⟩
  letI : Nontrivial P := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq P x y
    refine ⟨⟨u, 1, ?_⟩⟩
    intro hu1
    rw [hu1, one_smul] at hu
    exact hxy hu
  have hP : IsPGroup p P := hG.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  letI : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hZ := hP.to_subgroup (Subgroup.center P)
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (Subgroup.center P) := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzP : orderOf (z : P) = p := (Subgroup.orderOf_coe z).trans hz
  have hfree : ∀ x : X, ((z : P) : Equiv.Perm X) x ≠ x := by
    intro x hx
    have hz1 : (z : P) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq P x y
      change ((z : P) : Equiv.Perm X) y = y
      rw [← hu]
      change (z : P) • (u • x) = u • x
      rw [← mul_smul, ← Subgroup.mem_center_iff.mp z.property u, mul_smul]
      exact congrArg (fun t : X => u • t) hx
    have hp1 : p = 1 := by simpa only [hz1, orderOf_one] using hzP.symm
    exact (Fact.out : p.Prime).ne_one hp1
  obtain ⟨g, hg⟩ := (z : P).property
  refine ⟨g, ?_, ?_⟩
  · change orderOf (φ g) = p
    rw [hg, Subgroup.orderOf_coe]
    exact hzP
  · intro x hx
    apply hfree x
    change (φ g) x = x at hx
    rwa [hg] at hx

/-- All cycles of the actual lifted element have length p, and its
original cyclic-orbit quotient has exactly degree / p elements. Only the
permutation image, rather than the lift in G, is asserted to have order p.
Finiteness of G itself is unnecessary because its permutation image is
finite. -/
theorem pGroup_exists_semiregular_element
    {G X : Type*} [Group G] [MulAction G X] [Finite X] [Nontrivial X]
    [MulAction.IsPretransitive G X] (hG : IsPGroup p G) :
    ∃ g : G, orderOf (MulAction.toPermHom G X g) = p ∧
      (∀ x : X, MulAction.period g x = p) ∧
      (∀ x : X, Nat.card (MulAction.orbit (Subgroup.zpowers g) x) = p) ∧
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) = Nat.card X / p := by
  obtain ⟨g, hg, hfree⟩ := pGroup_exists_primeOrder_fixedPointFree_image (X := X) hG
  have hpow : (MulAction.toPermHom G X g) ^ p = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one _
  have hperiod : ∀ x : X, MulAction.period g x = p := by
    intro x
    apply Function.minimalPeriod_eq_prime
    · rw [MulAction.isPeriodicPt_smul_iff]
      change (MulAction.toPermHom G X (g ^ p)) x = x
      rw [map_pow, hpow]
      rfl
    · exact hfree x
  have hcard : ∀ x : X, Nat.card (MulAction.orbit (Subgroup.zpowers g) x) = p := by
    intro x
    rw [cyclicOrbit_eq_permutationImageOrbit]
    exact primeOrderPermutation_orbit_card _ hg hfree x
  refine ⟨g, hg, hperiod, hcard, ?_⟩
  have hmul := cyclicOrbitCount_mul_of_orbit_card g p hcard
  rw [← hmul, Nat.mul_div_cancel _ (Fact.out : p.Prime).pos]

end SymmetricSubgroupAsymptotics
