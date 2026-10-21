import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroCarryCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalKernelSpace
import SymmetricSubgroupAsymptotics.BinaryPairElementaryPhiZeroOuterCarries
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoCarryRank
import SymmetricSubgroupAsymptotics.BinaryElementaryTransitiveAbelianizationCard
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.PermutationBinaryHead

/-! In the elementary phi-zero critical case, order1024 in the full
original abelianization saturates the actual kernel extension. Literal
original-lift square carries then prove exponent two and ten ordinary
generators. No elementary-abelianization assumption is used beforehand. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance binaryDegreeThirtyTwoElementaryCarryConclusionFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem elementary_phi_zero_genRank_ten_of_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (hAb : Nat.card (Abelianization U) = 1024) : 10 ≤ MarkedC4.genRank U := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  have hTopAb : Nat.card (Abelianization F.top.range) = 16 := by
    simpa only [Nat.card_fin] using binary_elementary_transitive_abelianization_card
      F.top.range hel (0 : Fin 16)
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 6 := by
    have hh := twoGroup_permutationSubrepresentationHead_le_width hTop 4
      (by norm_num only [Nat.card_fin]) (0 : Fin 16) W
    rw [representationHead_finrank_eq_coinvariants] at hh
    norm_num at hh
    exact hh
  have hBupper : MarkedC4.normalGen F.top.ker ≤ 6 := by
    rw [F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hcap
  have hext := F.abelianization_card_le_actual_kernel_normalGen hU
  rw [hAb,hTopAb] at hext
  have hB : MarkedC4.normalGen F.top.ker = 6 := by
    by_contra h
    have hs : MarkedC4.normalGen F.top.ker ≤ 5 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hs
    norm_num at hp
    nlinarith
  have hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range) := by
    rw [hAb,hB,hTopAb]
    norm_num
  have hrad := F.relativeRadical_eq_inf_commutator_of_actual_abelianization_saturation hU hsat
  have hcoordRad := BinaryElementaryPhiZeroIntrinsicRadical.original_radical_eq
    E hzero hH hK W hS hcap
  let F' := F.reindex E.canonicalPointLabels
  have hrange : F'.top.range = Subgroup.closure
      (Set.range BinaryElementary16PhiZeroOuterCarries.generators) :=
    F.canonical_elementary_carry_top_range E hzero hH hK
  have hlift : ∀ i : Fin 4, ∃ u : U,
      F'.top u = BinaryElementary16PhiZeroOuterCarries.generators i := by
    intro i
    have hm : BinaryElementary16PhiZeroOuterCarries.generators i ∈ F'.top.range := by
      rw [hrange];exact Subgroup.subset_closure ⟨i,rfl⟩
    exact hm
  choose u hp using hlift
  have hgen : Subgroup.closure (Set.range fun i => F'.top (u i)) = F'.top.range := by
    rw [show (fun i => F'.top (u i)) = BinaryElementary16PhiZeroOuterCarries.generators
      from funext hp,hrange]
  have hpointK : F'.kernelSpace = BinaryElementary16PhiZeroOuterCarries.pointState := by
    have hh := F.canonical_kernelSpace_eq_comap E _ hS
    rw [BinaryElementaryPhiZeroCarryCoordinates.state_eq_wideState,
      ← BinaryElementaryPhiZeroCarryCoordinates.layerChange_eq] at hh
    exact hh
  have hradTransport (K : Subgroup U) [K.Normal] (he : F.top.ker = K) :
      primeRelativeRadical 2 K = K ⊓ commutator U := by
    subst K;exact hrad
  have hrad' : primeRelativeRadical 2 F'.top.ker = F'.top.ker ⊓ commutator U :=
    hradTransport _ (F.reindex_top_ker E.canonicalPointLabels).symm
  have hpointR : ∀ k : F'.top.ker,
      F'.bits k ∈ BinaryElementary16PhiZeroOuterCarries.pointRadical ↔
        (k : U) ∈ primeRelativeRadical 2 F'.top.ker := by
    intro k
    change BinaryElementary16PhiZeroOuterCarries.layerChange (F'.bits k) ∈
      BinaryElementary16PhiZeroOuterCarries.lowerRadical ↔ _
    rw [BinaryElementaryPhiZeroCarryCoordinates.layerChange_eq,
      ← BinaryElementaryPhiZeroCarryCoordinates.radical_eq_lowerRadical]
    exact F.canonical_bits_mem_radical_iff E _ hcoordRad k
  have hexp := ElementaryPhiZeroOuterCarries.abelianization_pow_two F' u hp hgen
    hpointK hrad' hpointR
  exact binary_genRank_ge_ten_of_full_abelianization_card_and_exponent hU hAb hexp

end SymmetricSubgroupAsymptotics.BinaryPairFrame
