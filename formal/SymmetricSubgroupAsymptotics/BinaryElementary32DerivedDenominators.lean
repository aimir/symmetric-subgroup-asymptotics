import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryDerivedModel
import SymmetricSubgroupAsymptotics.BinaryFiveHyperplaneCover

/-! Every original nonabelian quotient supplies a proper subspace of the
SAME five-dimensional original derived chart. A coordinate hyperplane
contains that actual intersection; no normal denominator is replaced by
a larger normal subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance elementaryDerivedDenominatorsFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))
    (E : BinaryPairFrame F.top.range (Fin 8))

include F E

theorem elementary_derived_denominator_hyperplane
    (hd : commutator U ≤ F.top.ker)
    (hcoord : (F.ambientAxis (commutator U)).map E.originalCoordinateEquiv.toLinearMap =
      BinaryElementaryPhiZeroIntrinsicRadical.radical.space)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ c : Fin 32, c≠0 ∧
      (F.ambientAxis (N ⊓ commutator U)).map E.originalCoordinateEquiv.toLinearMap ≤
        binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical c := by
  let L := N ⊓ commutator U
  have hLD : L ≤ commutator U := inf_le_right
  have haxis : F.ambientAxis L ≤ F.ambientAxis (commutator U) := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis L v).mp hv
    exact (F.mem_ambientAxis (commutator U) (F.bits k)).mpr ⟨k,hLD hk,rfl⟩
  have hAC : (F.ambientAxis L).map E.originalCoordinateEquiv.toLinearMap ≤
      BinaryElementaryPhiZeroIntrinsicRadical.radical.space := by
    rw [←hcoord]
    exact Submodule.map_mono haxis
  have hproper : (F.ambientAxis L).map E.originalCoordinateEquiv.toLinearMap ≠
      BinaryElementaryPhiZeroIntrinsicRadical.radical.space := by
    intro he
    have hae : F.ambientAxis L=F.ambientAxis (commutator U) :=
      (Submodule.map_injective_of_injective E.originalCoordinateEquiv.injective)
        (he.trans hcoord.symm)
    have hDL : commutator U ≤ L := by
      intro g hg
      let k : F.top.ker := ⟨g,hd hg⟩
      have hb : F.bits k∈F.ambientAxis L := by
        rw [hae]
        exact (F.bits_mem_ambientAxis (commutator U) k).mpr hg
      exact (F.bits_mem_ambientAxis L k).mp hb
    have hDN : commutator U ≤ N := hDL.trans inf_le_left
    letI : IsMulCommutative (U ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hDN
    exact hnonab (fun a b => mul_comm' a b)
  exact exists_nonzero_binaryFiveHyperplane_of_proper
    BinaryElementaryPhiZeroIntrinsicRadical.radical _ hAC hproper

end SymmetricSubgroupAsymptotics.BinaryPairFrame
