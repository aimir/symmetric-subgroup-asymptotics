import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryNormalFInstaller
import SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplanes

/-! Every original nonabelian quotient of a rank-ten elementary-top
thirty-two-point source has the exact coefficient5/4 normal-F packet.
The finite hyperplane capacities are supplied internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

include F

theorem elementary_rank_ten_normalF_packet
    [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (hhigh : 10≤MarkedC4.genRank U)
    (hpow : ∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      commutatorLog V+(5/4 : ℝ)*centralLog V≤16 ∧ centralLog V≤8 :=
  F.elementary_rank_ten_packet_of_hyperplane_capacities hU hhigh hpow
    BinaryElementary32DerivedHyperplanes.capacity_le N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
