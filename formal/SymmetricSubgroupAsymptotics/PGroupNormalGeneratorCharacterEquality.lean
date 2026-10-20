import SymmetricSubgroupAsymptotics.PrimeNormalIntervalCharacters
import SymmetricSubgroupAsymptotics.NormalGeneratorCharacterBound
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Relative Burnside basis theorem for literal ambient normal generation.
In a finite p-group, lifts of a basis of the whole-ambient relative prime
quotient normally generate the same original normal subgroup. A proper
normal closure would be annihilated by a nonzero invariant character on
that actual normal interval, contradicting the chosen dual basis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- A normally generating tuple of exactly the original relative-character
rank. The entries lie in the original normal subgroup. -/
theorem pGroup_exists_normal_generating_tuple_primeRelativeHead
    (hG : IsPGroup p G) (N : Subgroup G) [N.Normal] :
    ∃ x : Fin (Module.finrank (ZMod p) (primeRelativeCharacters p N)) → G,
      (∀ i, x i ∈ N) ∧ Subgroup.normalClosure (Set.range x) = N := by
  let R := primeRelativeCharacters p N
  let b : Module.Basis (Fin (Module.finrank (ZMod p) R)) (ZMod p)
      (Module.Dual (ZMod p) R) :=
    Module.finBasisOfFinrankEq (ZMod p) (Module.Dual (ZMod p) R) Subspace.dual_finrank_eq
  choose n hn using fun i => primeRelativeEvaluation_surjective p N (Multiplicative.ofAdd (b i))
  let x : Fin (Module.finrank (ZMod p) R) → G := fun i => (n i : G)
  let H := Subgroup.normalClosure (Set.range x)
  have hHN : H ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact (n i).property
  have hH : H = N := by
    by_contra he
    have hlt : H < N := lt_of_le_of_ne hHN he
    obtain ⟨χ, hχ, hvanish⟩ :=
      pGroup_exists_nonzero_relativeCharacter_vanishing hG H N hlt
    have hbzero (i : Fin (Module.finrank (ZMod p) R)) : b i χ = 0 := by
      have hentry : (n i : G) ∈ H := Subgroup.subset_normalClosure (Set.mem_range_self i)
      have heval := congrArg
        (fun z : Multiplicative (Module.Dual (ZMod p) R) => z.toAdd χ) (hn i)
      exact heval.symm.trans (hvanish (n i) hentry)
    have heval : Module.evalEquiv (ZMod p) R χ = 0 := by
      apply LinearMap.ext_on_range b.span_eq
      intro i
      exact hbzero i
    exact hχ ((Module.evalEquiv (ZMod p) R).injective
      (heval.trans (map_zero (Module.evalEquiv (ZMod p) R)).symm))
  exact ⟨x, fun i => (n i).property, hH⟩

/-- In a finite p-group the normal-generator number is exactly the head
under conjugation by the whole original ambient group. -/
theorem pGroup_normalGen_eq_primeRelativeHead
    (hG : IsPGroup p G) (N : Subgroup G) [N.Normal] :
    MarkedC4.normalGen N = Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  apply le_antisymm
  · obtain ⟨x, _, hx⟩ := pGroup_exists_normal_generating_tuple_primeRelativeHead p hG N
    exact normalGen_le_of_fin_tuple x hx
  · exact primeRelativeHead_le_normalGen p N

end SymmetricSubgroupAsymptotics
