import SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizer
import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowsCanonicalOrEscape
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage

/-! The regular elementary seed's actual normalizer overgroups retain the
same original points. Odd complement rows use literal word-bound canonical
charts; binary extensions recurse through the independently checked frontier. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizerCanonicalCoverage
open BinaryThreeAffineRowActions

theorem complete (U : Subgroup Ambient)
    (hHU : RegularEightElementaryNormalizer.H ≤ U)
    (hUN : U ≤ Subgroup.normalizer RegularEightElementaryNormalizer.H)
    (hnot : ¬IsPGroup 2 U) :
    BinaryThreeAffineRowsCanonicalOrEscape.Canonical U := by
  obtain ⟨i,c,hc⟩ := RegularEightElementaryNormalizer.complete U hHU hUN
  rcases BinaryThreeAffineRowsCanonicalOrEscape.complete i with hp | hcanon | hescape
  · exact (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U _ c hc hp)).elim
  · obtain ⟨j,d,hd⟩ := hcanon
    refine ⟨j,d*c,?_⟩
    rw [map_mul,mul_smul,hc]
    exact hd
  · have he := PermutationPrimePowerSeedEscape.conjugate 2 8 c⁻¹ _ hescape
    rw [←hc,map_inv,inv_smul_smul] at he
    obtain ⟨P,hPU,hp,ht,hcard⟩ := he
    exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizerCanonicalCoverage
end
