import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullProperAxisZero
import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullProperAxisConstant

/-! The two exceptional full-kernel axes are paid by proper normal
subgroups. The original quotient normal N remains arbitrary and identical
in both factors; no kernel-normal specialization is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart0 chart4 chart23 chart33 chart45)
open LinearSemidirectCoprimeSocleBounds

 theorem zero_axis_unit_packet (N : Subgroup Model) [N.Normal]
    (hNA : ∀ v : V, (SemidirectProduct.inl (Multiplicative.ofAdd v) : Model) ∈ N ↔
      v ∈ chart0.space) :
    ∃ W : Subgroup (Model ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  apply properNormalF_unit_packet action chart33.space chart4.space chart0.space (generators 0)
    BinaryHeisenbergFullProperAxisZero.carrier_le_body
    (chart0.le_of_basis_mem _ (by decide +kernel)) z_central
    BinaryHeisenbergFullProperAxisZero.carrier_stable
    BinaryHeisenbergFullProperAxisZero.body_displacement
    BinaryHeisenbergFullProperAxisZero.central_displacement
    (by rw [chart4.card,chart0.card]; decide) _ N hNA
  change Nat.card {v : V // rho (generators 0) v - v ∈ chart0.space} *
    Nat.card {t : H // ∀ v, v ∈ chart33.space → rho t v - v ∈ chart0.space} ≤ _
  rw [BinaryHeisenbergFullProperAxisZero.fixed_card,chart0.card]
  have h := BinaryHeisenbergFullProperAxisZero.top_card
  norm_num at h ⊢
  omega

 theorem constant_axis_unit_packet (N : Subgroup Model) [N.Normal]
    (hNA : ∀ v : V, (SemidirectProduct.inl (Multiplicative.ofAdd v) : Model) ∈ N ↔
      v ∈ chart23.space) :
    ∃ W : Subgroup (Model ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  apply properNormalF_unit_packet action chart45.space chart33.space chart23.space (generators 0)
    BinaryHeisenbergFullProperAxisConstant.carrier_le_body
    (chart23.le_of_basis_mem _ (by decide +kernel)) z_central
    BinaryHeisenbergFullProperAxisConstant.carrier_stable
    BinaryHeisenbergFullProperAxisConstant.body_displacement
    BinaryHeisenbergFullProperAxisConstant.central_displacement
    (by rw [chart33.card,chart23.card]; decide) _ N hNA
  change Nat.card {v : V // rho (generators 0) v - v ∈ chart23.space} *
    Nat.card {t : H // ∀ v, v ∈ chart45.space → rho t v - v ∈ chart23.space} ≤ _
  rw [BinaryHeisenbergFullProperAxisConstant.fixed_card,chart23.card]
  have h := BinaryHeisenbergFullProperAxisConstant.top_card
  norm_num at h ⊢
  omega

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
