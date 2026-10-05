import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeTranslationGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineNonzeroCore
import SymmetricSubgroupAsymptotics.PermutationSocleSectionSmallThree
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource

/-!
# Correlated degree-three source at three blocks

For a natural `S3` affine component on three blocks, the pointwise operation
which first estimates the six-point signed quotient and then prepends the
ternary translations loses the odd-width margin.  The correct source keeps
the original normal axis.

Axes containing the literal translation intersection are charged directly
to the faithful six-point quotient action.  On every other axis, Clifford
homogeneity splits the socle into its translation-active part and the part
carried by the actual three-point top.  The new ternary-width generator
theorem gives one generator for the first part, and the sharp three-point
section theorem gives one generator for the second.  The two parts share the
same slot through the existing action-type max theorem.  Zmud's published
faithful-character theorem then supplies the one-character cold row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev DegreeThreeLiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- In the nonzero signed-kernel branch at three blocks, every retained
normal quotient has one normally generating socle slot.  The statement is
on the literal original normal axis. -/
theorem degreeThreeThreeBlockNonzero_socleGenerators
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (N : DegreeThreeLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1) 1 := by
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
  let D := degreeNineWholeRetainedCore block P N
  have hsplit := degreeNineWholeCore_cliffordData block P hClifford
    hTraceyPerm hK N hretained
  have hmax := normalGen_finiteGroupSocle_le_max_actionSocleParts
    (preE7NonPairAction w U ⧸ N.1) D
  refine hmax.trans (max_le ?_ ?_)
  · rw [hsplit.1]
    have htranslation := degreeThreeTranslationSoclePart_normalGen_le
      block P hTraceyPerm hr i₀ N
    have hf : (3 : ℕ).factorization 3 = 1 := by decide +kernel
    rw [hs, hf] at htranslation
    norm_num [ternaryWidthCore] at htranslation ⊢
    exact htranslation
  · let R₀ : Subgroup (preE7NonPairAction w U ⧸ N.1) → Prop :=
      fun M ↦ ¬ ⁅D, M⁆ = M
    change MarkedC4.normalGen
      (minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1) R₀) ≤ 1
    apply threeBlockSelectedSoclePart_normalGen_le_one block P hs N R₀
    have hD : D = degreeFiveRetainedBlockKernel block P N := rfl
    change trivialActionSoclePart
      (preE7NonPairAction w U ⧸ N.1) D ⊓
        degreeFiveRetainedBlockKernel block P N = ⊥
    rw [← hD]
    exact hsplit.2

/-- Structural interval retaining the original translation subgroup. -/
noncomputable def degreeThreeThreeBlockNonzero_socleInterval
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := 1
  quotientSocleGenerators := fun N hN ↦
    degreeThreeThreeBlockNonzero_socleGenerators block P hClifford
      hTraceyPerm hr hs i₀ hK N hN

private theorem logb_two_five_lt_seven_thirds_degreeThree :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

/-- Final correlated source for the nonzero signed-kernel, three-block cell.
No finite action classification enters: the faithful quotient action and all
normal axes come from the actual block system. -/
noncomputable def degreeThreeThreeBlockNonzeroCorrelatedSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let I := degreeThreeThreeBlockNonzero_socleInterval block P hClifford
    hTraceyPerm hr hs i₀ hK
  let D := I.toCompleteCharacterIntervalData hZmud
  apply boundedCompleteCharacterSource D lit .acert
  · have hw9 : w = 9 := by
      simpa only [hr, hs] using width_eq block
    have hq6 : quotientDegree block = 6 := by
      rw [quotientDegree_eq, hr, hs]
    have hIq6 : I.quotientDegree = 6 := by
      simpa only [I, degreeThreeThreeBlockNonzero_socleInterval] using hq6
    have hDq6 : D.quotientDegree = 6 := by
      simpa only [D,
        SocleGeneratorCharacterIntervalData.toCompleteCharacterIntervalData_quotientDegree]
        using hIq6
    have hwR : (w : ℝ) = 9 := by exact_mod_cast hw9
    have heven : evenWidth w = 8 := by
      rw [hw9]
      norm_num [evenWidth, halfDegree]
    have hdegree : boundedCharacterSourceDegree D = 6 := by
      rw [boundedCharacterSourceDegree, hDq6]
      norm_num
    rw [hwR, heven, hdegree]
    norm_num [preE7CharacterRho]
  · have htheta : D.theta =
        (1 : ℝ) * (Real.logb 2 5 / 3) := by
      have hslots : I.slots = 1 := by
        rfl
      rw [show D.theta = (I.slots : ℝ) * (Real.logb 2 5 / 3) by
        exact SocleGeneratorCharacterIntervalData.toCompleteCharacterIntervalData_theta
          I hZmud]
      rw [hslots]
      norm_num
    have hw9 : w = 9 := by
      simpa only [hr, hs] using width_eq block
    have hwR : (w : ℝ) = 9 := by exact_mod_cast hw9
    have hhalf : halfDegree w = 4 := by
      rw [hw9]
      norm_num [halfDegree]
    have hlog := logb_two_five_lt_seven_thirds_degreeThree
    rw [htheta]
    unfold preE7CharacterWindow
    rw [hhalf, hwR]
    norm_num [preE7CharacterRho]
    linarith
  · have hw9 : w = 9 := by
      simpa only [hr, hs] using width_eq block
    omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
