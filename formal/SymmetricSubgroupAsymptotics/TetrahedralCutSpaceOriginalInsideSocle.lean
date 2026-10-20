import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalHeads
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalInsideSocle
open OriginalKernelModuleChart
open AlternatingEdgeOriginalProjectorHeads (Top)
open TetrahedralCutSpaceOriginalHeads (R)

theorem socle_bound {G : Type} [Group G] [Finite G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (E : OriginalKernelModuleChart pi R)
    (N : Subgroup G) [N.Normal]
    (hinside : finiteGroupSocle (G ⧸ N)≤(base pi N).ker) :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi R N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi R N)
    infer_instance
  have hR : UniformSubrepresentationGeneratorBound R.ρ 1 :=
    TetrahedralCutSpaceRepresentation.uniform_one
  have hs := E.sectionUniform pi R N hpi hR
  have hn : MarkedC4.normalGen (finiteGroupSocle (G ⧸ N))≤1 :=
    (E.quotientChart pi R N).kernel_normalGen_le (base pi N)
      (E.sectionRepresentation pi R N) (base_surjective pi N) 1 hs _ hinside
  exact (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 1).mpr hn
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalInsideSocle
