import SymmetricSubgroupAsymptotics.S8Seed3OvergroupCoverage
import SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizerCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport

/-! The original regular elementary seed's exact finite forest retains its
normalizer target. Actual affine point coverage handles that target; every
escape retains a larger transitive binary subgroup inside the SAME group. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed3CanonicalCoverage
open S8Seed3LeftCosets

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬IsPGroup 2 U) :
    BinaryThreeAffineRowsCanonicalOrEscape.Canonical U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [←hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  have hnot' : ¬IsPGroup 2 ↥(MulAut.conj c • U) := by
    intro hp
    exact hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U _ c rfl hp)
  rcases S8Seed3OvergroupCoverage.complete (MulAut.conj c • U) hHU with hnormal | hescape
  · obtain ⟨j,d,hd⟩ := RegularEightElementaryNormalizerCanonicalCoverage.complete
      (MulAut.conj c • U) hHU hnormal hnot'
    refine ⟨j,d*c,?_⟩
    rw [map_mul,mul_smul]
    exact hd
  · have he := PermutationPrimePowerSeedEscape.conjugate 2 8 c⁻¹ _ hescape
    rw [map_inv,inv_smul_smul] at he
    obtain ⟨P,hPU,hp,ht,hcard⟩ := he
    exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed3CanonicalCoverage
end
