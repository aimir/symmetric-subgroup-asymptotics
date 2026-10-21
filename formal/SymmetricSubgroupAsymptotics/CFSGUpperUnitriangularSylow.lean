import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularPGroup
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! Exact assembly of the actual unitriangular Sylow subgroup from its
literal Borel normalizer containment. The containment is an explicit
structural lemma parameter here, not a classification or order premise;
concrete family adapters must install its proved matrix theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular

def sylowOfBorelNormalizer (F : Type*) [Field F] [Finite F]
    (p n : ℕ) [Fact p.Prime] [CharP F p]
    (hN : Subgroup.normalizer (upperUnitriangular F n : Set (SL F n))≤borel F n) :
    Sylow p (SL F n) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (upperUnitriangular F n)
    (upperUnitriangular_isPGroup n)
    (fun P hP hPN => pSubgroup_le_upperUnitriangular P hP (hPN.trans hN))

@[simp] theorem sylowOfBorelNormalizer_coe (F : Type*) [Field F] [Finite F]
    (p n : ℕ) [Fact p.Prime] [CharP F p]
    (hN : Subgroup.normalizer (upperUnitriangular F n : Set (SL F n))≤borel F n) :
    (sylowOfBorelNormalizer F p n hN : Subgroup (SL F n))=upperUnitriangular F n := rfl

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
