import SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary
import SymmetricSubgroupAsymptotics.SylowNonelementaryPermutationQuarterGenerators
import SymmetricSubgroupAsymptotics.BinarySixteenTwoGroupSharpStep
import SymmetricSubgroupAsymptotics.BinaryBlockCentralBinomialOrdinaryStep
import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction

/-! The original binary-fibre degree-sixteen sharp step retains the SAME
actual eight-point top and its kernel module. Nonelementary top Sylows
pay the quarter module cost; elementary top Sylows pay top rank three.
The sole model obstruction is the actual relabeled primitive sporadic
TOP of rank greater than three. A separate global failed-half action is
retained only when the proved eight-point half-degree reduction returns
one. No transitive-eight rank-three assertion is assumed universally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalBinarySixteenSharpCFSGReduction
open EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

variable (J : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive J (Fin 16)] {x₀ : Fin 16}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem genRank_le_six_or_actual_top_sporadic_or_global_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 2) :
    MarkedC4.genRank J ≤ 6 ∨
      Nonempty (ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
        (G := block.Top) (X := block.Points)) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  have hprod : 2*Nat.card block.Points = 16 := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 8 := by omega
  letI : Nonempty block.Points := ⟨block.base⟩
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x₀).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x₀ block.subgroup block.covers.le
  let pair : TransitiveBinaryPairCover J x₀ :=
    ⟨block.subgroup,block.covers,hrel.symm.trans hr⟩
  let F := pair.frame
  have hact (g : J) (i : block.Points) : g • i = F.top g i := rfl
  by_cases hbinary : IsPGroup 2 block.Top
  · exact Or.inl (BinarySixteenTwoGroupSharpStep.genRank_le_six J
      (F.source_isPGroup_of_top_isPGroup hbinary) (by simp only [Nat.card_fin]))
  let Q : Sylow 2 block.Top := Classical.choice inferInstance
  by_cases hel : ∀ q : Q, q^2 = 1
  · rcases ElementarySylowEightFaithfulActionOrdinary.genRank_le_three_or_actual_sporadic
      hCFSG Q hel ht with htop | hbad
    · have hh := BinaryBlockCentralBinomialOrdinaryStep.genRank_le_top_add_middle
        F hact block.base 3 ht
      change MarkedC4.genRank J ≤ MarkedC4.genRank block.Top + 3 at hh
      exact Or.inl (by omega)
    · exact Or.inr (Or.inl hbad)
  have hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := Q) (X := block.Points) :=
    fun h => hel (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp h)
  have huTop := SylowNonelementaryPermutationQuarterGenerators.permutation_uniform
    Q 3 ht hnon
  have hu := UniformSubrepresentationGeneratorBound.comp_of_surjective
    (permutationFunctionRepresentation (ZMod 2) block.Top block.Points)
      block.topMap.rangeRestrict block.topMap.rangeRestrict_surjective huTop
  have he : (permutationFunctionRepresentation (ZMod 2) block.Top block.Points).comp
      block.topMap.rangeRestrict = permutationFunctionRepresentation (ZMod 2) J block.Points := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    funext i
    change v ((block.topMap g)⁻¹ i) = v (block.topMap (g⁻¹) i)
    rw [map_inv]
  rw [he] at hu
  have hu' : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) J block.Points) 2 := by
    simpa only [ht] using hu
  have hk := F.normalGen_le_of_uniform_pair_module hact 2 hu' F.top.ker le_rfl
  let pi : J →* F.top.range := F.top.rangeRestrict
  letI : IsMulCommutative pi.ker := by
    change IsMulCommutative F.top.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact BinaryBlockOrdinaryGeneratorInduction.kernel_isMulCommutative F
  have hk' : MarkedC4.normalGen pi.ker ≤ 2 := by
    change MarkedC4.normalGen F.top.rangeRestrict.ker ≤ 2
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hrec := (AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    pi F.top.rangeRestrict_surjective).trans (Nat.add_le_add_left hk' _)
  change MarkedC4.genRank J ≤ MarkedC4.genRank block.Top + 2 at hrec
  rcases EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
    hCFSG (G := block.Top) (X := block.Points) (by omega) (by omega) with hh | hbad
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr hbad)

theorem genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 2) :
    MarkedC4.genRank J ≤ sharpFloor 16 ∨
      Nonempty (ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
        (G := block.Top) (X := block.Points)) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_six_or_actual_top_sporadic_or_global_counterexample J block hCFSG hr with
    hh | htop | hglobal
  · have hsix : 6 ≤ sharpFloor 16 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
      16 6 4 (by decide)
        (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 16 4 (by decide) (by decide)) (by decide)
    exact Or.inl (hh.trans hsix)
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)

end SymmetricSubgroupAsymptotics.OriginalBinarySixteenSharpCFSGReduction
