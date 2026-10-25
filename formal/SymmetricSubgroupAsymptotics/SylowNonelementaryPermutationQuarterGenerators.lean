import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive
import SymmetricSubgroupAsymptotics.BinaryBlockOrdinaryGeneratorInduction

/-! An actual Sylow two-subgroup is transitive on a prime-power block
set. If its SAME block action is nonelementary, the proved quarter-module
theorem restricts and then enlarges back to the original acting group.
This pays a correlated original binary kernel without a whole-source
two-group hypothesis or any current-degree generator bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SylowNonelementaryPermutationQuarterGenerators

theorem permutation_uniform
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (P : Sylow 2 G) (k : ℕ) (hcard : Nat.card X = 2^k)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := P) (X := X)) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G X) (Nat.card X / 4) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive P X := sylow_isPretransitive_of_card_eq_prime_pow P hcard
  have hu := twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary
    P.isPGroup' hnon
  apply UniformSubrepresentationGeneratorBound.of_comp
    (permutationFunctionRepresentation (ZMod 2) G X) (P : Subgroup G).subtype
  change UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) P X) (Nat.card X / 4)
  exact hu

variable {Ω I : Type} [Finite Ω] [Finite I] [Nonempty I]
    {J : Subgroup (Equiv.Perm Ω)} (F : BinaryPairFrame J I)
    [MulAction J I] [MulAction.IsPretransitive J I]
    (hact : ∀ (g : J) (i : I), g • i = F.top g i)

include hact in
theorem genRank_le_top_add_quarter (P : Sylow 2 J) (k : ℕ) (hcard : Nat.card I = 2^k)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := P) (X := I)) :
    MarkedC4.genRank J ≤ MarkedC4.genRank F.top.range + Nat.card I / 4 := by
  have hu := permutation_uniform P k hcard hnon
  have hk := F.normalGen_le_of_uniform_pair_module hact (Nat.card I / 4) hu F.top.ker le_rfl
  let pi : J →* F.top.range := F.top.rangeRestrict
  letI : IsMulCommutative pi.ker := by
    change IsMulCommutative F.top.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact BinaryBlockOrdinaryGeneratorInduction.kernel_isMulCommutative F
  have hk' : MarkedC4.normalGen pi.ker ≤ Nat.card I / 4 := by
    change MarkedC4.normalGen F.top.rangeRestrict.ker ≤ _
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hh := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    pi F.top.rangeRestrict_surjective
  exact hh.trans (Nat.add_le_add_left hk' _)

end SymmetricSubgroupAsymptotics.SylowNonelementaryPermutationQuarterGenerators
