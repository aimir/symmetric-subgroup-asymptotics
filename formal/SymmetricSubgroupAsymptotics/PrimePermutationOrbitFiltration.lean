import SymmetricSubgroupAsymptotics.PrimeCoordinateRanks
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Prime-character excess is witnessed on an actual original orbit

Restrict one original permutation subgroup simultaneously to all of its
literal orbits.  The restriction maps are jointly faithful and onto their
literal images.  The full-coordinate relative-head theorem therefore puts
any excess over an additive degree budget into a normal subgroup of one
actual orbit image.  No abstract product action or replacement orbit is
introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- If the prime-character rank of an original permutation subgroup exceeds
an additive multiple of its degree, one literal orbit image contains a
normal pair whose relative head exceeds the same local multiple. -/
theorem primeCharacterRank_actualOrbit_high
    {X : Type*} [Finite X] (H : Subgroup (Equiv.Perm X))
    (a q : ℕ) (hq : 0 < q)
    (hhigh : a * Nat.card X <
      q * Module.finrank (ZMod p) (PrimeCharacters p H)) :
    ∃ o : OrbitProfileFromOrbits.Orbit H,
      ∃ (N : Subgroup (OrbitProfileFromOrbits.orbitImage H o)) (hN : N.Normal),
        letI := hN
        a * Nat.card o.orbit <
          q * Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  classical
  let O := OrbitProfileFromOrbits.Orbit H
  letI : Fintype O := Fintype.ofFinite O
  let n := Fintype.card O
  let e : Fin n ≃ O := (Fintype.equivFin O).symm
  let A (i : Fin n) :=
    ↥(OrbitProfileFromOrbits.orbitImage H (e i))
  let ρ (i : Fin n) : H →* A i :=
    (MulAction.toPermHom H (e i).orbit).rangeRestrict
  have honto : ∀ i, Function.Surjective (ρ i) := by
    intro i
    exact (MulAction.toPermHom H (e i).orbit).rangeRestrict_surjective
  have hfaithful : Function.Injective (fun h : H => fun i => ρ i h) := by
    intro g h hgh
    apply Subtype.ext
    apply Equiv.ext
    intro x
    let o : O := Quotient.mk'' x
    obtain ⟨i, hi⟩ := e.surjective o
    have hx : x ∈ (e i).orbit := by
      rw [hi]
      exact MulAction.mem_orbit_self x
    have hc := congrFun hgh i
    have hp := Equiv.congr_fun (congrArg Subtype.val hc) ⟨x, hx⟩
    exact congrArg Subtype.val hp
  let w (i : Fin n) := a * Nat.card (e i).orbit
  have horbits : ∑ o : O, Nat.card o.orbit = Nat.card X := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (MulAction.selfEquivSigmaOrbits' H X).symm
  have hweights : ∑ i, w i = a * Nat.card X := by
    dsimp only [w]
    rw [← Finset.mul_sum]
    exact congrArg (fun z => a * z)
      ((e.sum_comp (fun o : O => Nat.card o.orbit)).trans horbits)
  have hhigh' : ∑ i, w i <
      q * Module.finrank (ZMod p) (PrimeCharacters p H) := by
    rw [hweights]
    exact hhigh
  obtain ⟨i, N, hN, hi⟩ := primeCharacterRank_faithful_family_high p n A ρ
    honto hfaithful w q hq hhigh'
  exact ⟨e i, N, hN, hi⟩

/-- Uniform relative-head capacity on every normal pair in every actual
orbit image implies the corresponding global capacity for the original
permutation subgroup. -/
theorem primeCharacterRank_actualOrbit_cap
    {X : Type*} [Finite X] (H : Subgroup (Equiv.Perm X))
    (a q : ℕ) (hq : 0 < q)
    (hcap : ∀ (o : OrbitProfileFromOrbits.Orbit H)
      (N : Subgroup (OrbitProfileFromOrbits.orbitImage H o)) (hN : N.Normal),
        letI := hN
        q * Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
          a * Nat.card o.orbit) :
    q * Module.finrank (ZMod p) (PrimeCharacters p H) ≤
      a * Nat.card X := by
  by_contra h
  have hhigh : a * Nat.card X <
      q * Module.finrank (ZMod p) (PrimeCharacters p H) := by omega
  obtain ⟨o, N, hN, hlocal⟩ :=
    primeCharacterRank_actualOrbit_high p H a q hq hhigh
  exact (Nat.not_lt_of_ge (hcap o N hN)) hlocal

/-- The exact all-orbit interface needed by the surviving C3 high-rank
branch: local relative `3/20` capacity forces global `3/20` capacity. -/
theorem ternaryCharacterRank_actualOrbit_three_twentieths
    {X : Type*} [Finite X] (H : Subgroup (Equiv.Perm X))
    (hcap : ∀ (o : OrbitProfileFromOrbits.Orbit H)
      (N : Subgroup (OrbitProfileFromOrbits.orbitImage H o)) (hN : N.Normal),
        letI := hN
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
          3 * Nat.card o.orbit) :
    20 * Module.finrank (ZMod 3) (PrimeCharacters 3 H) ≤
      3 * Nat.card X := by
  exact primeCharacterRank_actualOrbit_cap 3 H 3 20 (by omega) hcap

end SymmetricSubgroupAsymptotics

end
