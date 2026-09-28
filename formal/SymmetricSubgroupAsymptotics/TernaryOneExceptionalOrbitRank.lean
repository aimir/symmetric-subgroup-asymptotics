import SymmetricSubgroupAsymptotics.PrimePermutationOrbitFiltration

/-!
# One exceptional orbit in the ternary permutation-rank sum

The complete source is retained throughout.  If every relative normal head
in every literal orbit image costs at most two ninths of that orbit, except
for one distinguished orbit which receives one additional third, then the
same exact budget holds for the original permutation subgroup.

This is only the orbit aggregation.  Identifying the distinguished orbit as
the actual regular C3 orbit and proving the local ordinary-orbit estimates
remain separate structural inputs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- One literal exceptional orbit accounts for the `+3` in
`9 d₃(H) ≤ 2 |X| + 3`.  All coordinate groups and normal axes are the
actual restriction images of the same original subgroup `H`. -/
theorem ternaryCharacterRank_oneExceptionalOrbit
    {X : Type*} [Finite X] (H : Subgroup (Equiv.Perm X))
    (exceptional : OrbitProfileFromOrbits.Orbit H)
    (hcap : ∀ (o : OrbitProfileFromOrbits.Orbit H)
      (N : Subgroup (OrbitProfileFromOrbits.orbitImage H o)) (hN : N.Normal),
        letI := hN
        9 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
          2 * Nat.card o.orbit + if o = exceptional then 3 else 0) :
    9 * Module.finrank (ZMod 3) (PrimeCharacters 3 H) ≤ 2 * Nat.card X + 3 := by
  classical
  let O := OrbitProfileFromOrbits.Orbit H
  letI : Fintype O := Fintype.ofFinite O
  let n := Fintype.card O
  let e : Fin n ≃ O := (Fintype.equivFin O).symm
  let A (i : Fin n) := ↥(OrbitProfileFromOrbits.orbitImage H (e i))
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
  let i₀ : Fin n := e.symm exceptional
  let w (i : Fin n) := 2 * Nat.card (e i).orbit + if i = i₀ then 3 else 0
  have horbits : ∑ o : O, Nat.card o.orbit = Nat.card X := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (MulAction.selfEquivSigmaOrbits' H X).symm
  have hweights : ∑ i, w i = 2 * Nat.card X + 3 := by
    dsimp only [w]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [e.sum_comp (fun o : O => Nat.card o.orbit), horbits]
    simp only [i₀, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_contra h
  have hhigh : ∑ i, w i <
      9 * Module.finrank (ZMod 3) (PrimeCharacters 3 H) := by
    rw [hweights]
    omega
  obtain ⟨i, N, hN, hi⟩ := primeCharacterRank_faithful_family_high
    3 n A ρ honto hfaithful w 9 (by omega) hhigh
  have hlocal := hcap (e i) N hN
  have hif : (if i = i₀ then 3 else 0) =
      if e i = exceptional then 3 else 0 := by
    by_cases hi₀ : i = i₀
    · subst i
      simp only [i₀, e.apply_symm_apply, ↓reduceIte]
    · have hei : e i ≠ exceptional := by
        intro he
        apply hi₀
        apply e.injective
        rw [he]
        exact (e.apply_symm_apply exceptional).symm
      simp only [hi₀, hei, ↓reduceIte]
  change 2 * Nat.card (e i).orbit + (if i = i₀ then 3 else 0) <
    9 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) at hi
  rw [hif] at hi
  exact (Nat.not_lt_of_ge hlocal) hi

end SymmetricSubgroupAsymptotics

end
