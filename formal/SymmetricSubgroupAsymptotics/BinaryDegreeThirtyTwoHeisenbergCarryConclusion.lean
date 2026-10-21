import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCarryCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalKernelSpace
import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergPhiZeroOuterCarries
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoCarryRank
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenRankSixAbelianization
import SymmetricSubgroupAsymptotics.BinaryHeisenbergCanonicalCarryTop
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoAbelianizationSaturation
import SymmetricSubgroupAsymptotics.PermutationBinaryHead

/-! In the Heisenberg phi-zero critical case, order1024 in the full
original abelianization saturates the actual kernel extension. Literal
original-lift square carries then prove exponent two and ten ordinary
generators. No elementary-abelianization assumption is used beforehand. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem heisenberg_phi_zero_genRank_ten_of_abelianization_card
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryHeisenbergEightNaturalHeads.H)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (hTopRank : 6 ≤ MarkedC4.genRank F.top.range)
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space)
    (hAb : Nat.card (Abelianization U) = 1024) : 10 ≤ MarkedC4.genRank U := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  have hTopAb : Nat.card (Abelianization F.top.range) = 64 :=
    binary_degree_sixteen_abelianization_card_of_rank_six F.top.range hTop
      (by norm_num only [Nat.card_fin]) hTopRank
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4 := by
    obtain ⟨v,hv⟩ := twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary
      hTop hnon W
    have hh := representationHead_finrank_le_generators W.toRepresentation v hv
    rw [representationHead_finrank_eq_coinvariants] at hh
    norm_num only [Nat.card_fin] at hh
    exact hh
  have hBupper : MarkedC4.normalGen F.top.ker ≤ 4 := by
    rw [F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hcap
  have hext := F.abelianization_card_le_actual_kernel_normalGen hU
  rw [hAb,hTopAb] at hext
  have hB : MarkedC4.normalGen F.top.ker = 4 := by
    by_contra h
    have hs : MarkedC4.normalGen F.top.ker ≤ 3 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hs
    norm_num at hp
    nlinarith
  have hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range) := by
    rw [hAb,hB,hTopAb]
    norm_num
  have hrad := F.relativeRadical_eq_inf_commutator_of_actual_abelianization_saturation hU hsat
  have hcoordRad := BinaryHeisenbergPhiZeroIntrinsicRadical.original_radical_eq
    E hzero hH hK W hS hcap
  let F' := F.reindex E.canonicalPointLabels
  have hrange : F'.top.range = Subgroup.closure
      (Set.range BinaryHeisenberg14PhiZeroOuterCarries.generators) :=
    F.canonical_heisenberg_carry_top_range E hzero hH hK
  have hlift : ∀ i : Fin 6, ∃ u : U,
      F'.top u = BinaryHeisenberg14PhiZeroOuterCarries.generators i := by
    intro i
    have hm : BinaryHeisenberg14PhiZeroOuterCarries.generators i ∈ F'.top.range := by
      rw [hrange];exact Subgroup.subset_closure ⟨i,rfl⟩
    exact hm
  choose u hp using hlift
  have hgen : Subgroup.closure (Set.range fun i => F'.top (u i)) = F'.top.range := by
    rw [show (fun i => F'.top (u i)) = BinaryHeisenberg14PhiZeroOuterCarries.generators
      from funext hp,hrange]
  have hpointK : F'.kernelSpace = BinaryHeisenberg14PhiZeroOuterCarries.pointState := by
    have hh := F.canonical_kernelSpace_eq_comap E _ hS
    rw [BinaryHeisenbergPhiZeroCarryCoordinates.state_eq_wideState,
      ← BinaryHeisenbergPhiZeroCarryCoordinates.layerChange_eq] at hh
    exact hh
  have hradTransport (K : Subgroup U) [K.Normal] (he : F.top.ker = K) :
      primeRelativeRadical 2 K = K ⊓ commutator U := by
    subst K;exact hrad
  have hrad' : primeRelativeRadical 2 F'.top.ker = F'.top.ker ⊓ commutator U :=
    hradTransport _ (F.reindex_top_ker E.canonicalPointLabels).symm
  have hpointR : ∀ k : F'.top.ker,
      F'.bits k ∈ BinaryHeisenberg14PhiZeroOuterCarries.pointRadical ↔
        (k : U) ∈ primeRelativeRadical 2 F'.top.ker := by
    intro k
    change BinaryHeisenberg14PhiZeroOuterCarries.layerChange (F'.bits k) ∈
      BinaryHeisenberg14PhiZeroOuterCarries.lowerRadical ↔ _
    rw [BinaryHeisenbergPhiZeroCarryCoordinates.layerChange_eq,
      ← BinaryHeisenbergPhiZeroCarryCoordinates.radical_eq_lowerRadical]
    exact F.canonical_bits_mem_radical_iff E _ hcoordRad k
  have hexp := HeisenbergPhiZeroOuterCarries.abelianization_pow_two F' u hp hgen
    hpointK hrad' hpointR
  exact binary_genRank_ge_ten_of_full_abelianization_card_and_exponent hU hAb hexp

end SymmetricSubgroupAsymptotics.BinaryPairFrame
