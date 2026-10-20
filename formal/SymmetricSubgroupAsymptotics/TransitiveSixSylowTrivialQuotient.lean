import SymmetricSubgroupAsymptotics.PermutationTrivialQuotientOrbitBound
import SymmetricSubgroupAsymptotics.TraceySylowIndices

/-! Any actual trivial quotient of a binary permutation submodule on six
transitive points has dimension at most two after restriction to a Sylow3.
The same source submodule and quotient map are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance transitiveSixSylowTrivialQuotientPrime3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G W : Type} [Group G] [Finite G]
    [MulAction G (Fin 6)] [MulAction.IsPretransitive G (Fin 6)]
    [AddCommGroup W] [Module (ZMod 2) W]

/-- The order of the actual Sylow3 is invertible in the original field. -/
theorem sylowThree_card_binary_neZero (P : Sylow 3 G) :
    (Nat.card P : ZMod 2) ≠ 0 := by
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  rw [hn,Nat.cast_pow]
  exact pow_ne_zero n (show ((3 : ℕ) : ZMod 2) ≠ 0 by decide +kernel)

/-- No classification, splitting or enlargement of the actual module. -/
theorem transitiveSix_sylowThree_trivial_quotient_finrank_le_two
    (P : Sylow 3 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) P (Fin 6)))
    (q : M.toSubmodule →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : P) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    Module.finrank (ZMod 2) W ≤ 2 := by
  classical
  letI : NeZero (Nat.card P : ZMod 2) := ⟨sylowThree_card_binary_neZero P⟩
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient P (Fin 6))
  have hqbound := permutation_trivial_quotient_finrank_le_orbits M q hq htrivial
  have ho := traceySylow_orbit_count 3 P (X := Fin 6)
  have ho' : Nat.card (MulAction.orbitRel.Quotient P (Fin 6)) * 3 ≤ 6 := by
    simpa only [Nat.card_fin,show Nat.factorization 6 3 = 1 by decide +kernel,
      pow_one,Nat.card_eq_fintype_card,Fintype.card_fin] using ho
  omega

end SymmetricSubgroupAsymptotics
end
