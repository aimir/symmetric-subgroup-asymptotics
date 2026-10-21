import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoFullConstantNormalIndex
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantStateBinding
import SymmetricSubgroupAsymptotics.BinaryPairRegularCanonicalTopRange
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalKernelSpace
import SymmetricSubgroupAsymptotics.BinaryPairRegularFullConstantOuterCarries
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenRankSixAbelianization
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoCarryRank

/-! The full-constant critical case concludes ten ordinary generators in
the same original degree-thirty-two source. The actual normal first
contains the full pair kernel; its own index then supplies order 1024.
Only the literal original-lift carry theorem eliminates higher cyclic
factors in the full abelianization. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped commutatorElement Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

/-- All hypotheses are literal intermediates in the original
intersection/image saturation case, not new classification inputs. -/
theorem fullconstant_case_genRank_ten
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (hTopRank : 6 ≤ MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        BinarySplitRegular46FullConstantStabilizer.state.space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 4)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : 10 ≤ MarkedC4.genRank U := by
  have hcontains := (F.fullconstant_normal_contains_kernel_and_index_two E hU
    hzero hH hK N hS hB hindex hcomm).1
  have hInf : N ⊓ F.top.ker = F.top.ker := inf_eq_right.mpr hcontains
  have hBwhole : MarkedC4.normalGen F.top.ker = 4 := by simpa only [hInf] using hB
  have hSwhole : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        BinarySplitRegular46FullConstantStabilizer.state.space := by
    simpa only [hInf] using hS
  have hAb := F.fullconstant_normal_abelianization_card E hU hzero hH hK N
    hS hB hindex hcomm hN
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTopAb := binary_degree_sixteen_abelianization_card_of_rank_six
    F.top.range (F.top_isPGroup hU) (by norm_num only [Nat.card_fin]) hTopRank
  have hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range) := by
    rw [hAb,hBwhole,hTopAb]
    norm_num
  have hrad := F.relativeRadical_eq_inf_commutator_of_actual_abelianization_saturation hU hsat
  have hcap : Module.finrank (ZMod 2)
      (F.axisNaturalSubrepresentation F.top.ker).toRepresentation.Coinvariants ≤ 4 := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU,hBwhole]
  have hcoordRad := BinarySplitRegular46FullConstantOriginalRadical.original_radical_eq
    E hzero hH hK (F.axisNaturalSubrepresentation F.top.ker) hSwhole hcap
  let F' := F.reindex E.canonicalPointLabels
  have hrange : F'.top.range = Subgroup.closure
      (Set.range BinaryRegular46FullConstantOuterCarries.generators) := by
    have hh := F.canonical_regular_top_range E hzero hH hK
    rw [BinaryRegular46FullConstantStateBinding.generators_eq] at hh
    exact hh
  have hlift : ∀ i : Fin 6, ∃ u : U,
      F'.top u = BinaryRegular46FullConstantOuterCarries.generators i := by
    intro i
    have hm : BinaryRegular46FullConstantOuterCarries.generators i ∈ F'.top.range := by
      rw [hrange]
      exact Subgroup.subset_closure ⟨i,rfl⟩
    exact hm
  choose u hp using hlift
  have hgen : Subgroup.closure (Set.range fun i => F'.top (u i)) = F'.top.range := by
    rw [show (fun i => F'.top (u i)) = BinaryRegular46FullConstantOuterCarries.generators
      from funext hp,hrange]
  have hpointK : F'.kernelSpace = BinaryRegular46FullConstantOuterCarries.pointState := by
    have hh := F.canonical_kernelSpace_eq_comap E _ hSwhole
    rw [BinaryRegular46FullConstantStateBinding.state_eq_wideState,
      ← BinaryRegular46FullConstantStateBinding.layerChange_eq] at hh
    exact hh
  have hradTransport (K : Subgroup U) [K.Normal] (he : F.top.ker = K) :
      primeRelativeRadical 2 K = K ⊓ commutator U := by
    subst K
    exact hrad
  have hrad' : primeRelativeRadical 2 F'.top.ker = F'.top.ker ⊓ commutator U :=
    hradTransport _ (F.reindex_top_ker E.canonicalPointLabels).symm
  have hpointR : ∀ k : F'.top.ker,
      F'.bits k ∈ BinaryRegular46FullConstantOuterCarries.pointRadical ↔
        (k : U) ∈ primeRelativeRadical 2 F'.top.ker := by
    intro k
    change BinaryRegular46FullConstantOuterCarries.layerChange (F'.bits k) ∈
      BinaryRegular46FullConstantOuterCarries.lowerRadical ↔ _
    rw [BinaryRegular46FullConstantStateBinding.layerChange_eq,
      ← BinaryRegular46FullConstantRadicalBinding.radical_eq_lowerRadical]
    exact F.canonical_bits_mem_radical_iff E _ hcoordRad k
  have hexp := RegularFullConstantOuterCarries.abelianization_pow_two F' u hp hgen
    hpointK hrad' hpointR
  exact binary_genRank_ge_ten_of_full_abelianization_card_and_exponent hU hAb hexp

end SymmetricSubgroupAsymptotics.BinaryPairFrame
