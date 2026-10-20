import SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryUniform
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalInsideSocle
open AlternatingEdgeOriginalProjectorHeads (Top beta)
open OriginalKernelModuleChart

theorem socle_bound {G : Type} [Group G] [Finite G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) Top) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ beta) (hj : Function.Injective j)
    (N : Subgroup G) [N.Normal]
    (hinside : finiteGroupSocle (G ⧸ N)≤(base pi N).ker) :
    SocleNormalGeneratorBound (G ⧸ N) 2 := by
  letI : Finite A := Finite.of_injective j hj
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi A N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  have hA : UniformSubrepresentationGeneratorBound A.ρ 2 :=
    AlternatingEdgeBinaryUniform.uniform.of_injective j hj
  have hs := E.sectionUniform pi A N hpi hA
  have hn : MarkedC4.normalGen (finiteGroupSocle (G ⧸ N))≤2 :=
    (E.quotientChart pi A N).kernel_normalGen_le (base pi N)
      (E.sectionRepresentation pi A N) (base_surjective pi N) 2 hs _ hinside
  exact (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 2).mpr hn

end SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalInsideSocle
