import SymmetricSubgroupAsymptotics.CFSGSuzukiGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiBruhatDecomposition
import SymmetricSubgroupAsymptotics.CFSGSuzukiOppositeGeneration

/-! Final literal Suzuki family installer. The temporary structural
parameters are supplied by the original-matrix normalizer-intersection
and opposite-unipotent generation theorems. No mathematical premise is
left in the family witness. The classifier's m≥1 guard is explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiModelGoodSylow

theorem goodSylowPrime (m : ℕ) :
    CFSGReduction.GoodSylowPrime (CFSG.Models.Suzuki m) 2 :=
  CFSGSuzukiGoodSylow.goodSylowPrime_of_normalizer_and_opposite m
    (CFSGSuzukiUnipotent.normalizer_inter_model_le_borel m)
    (CFSGSuzukiUnipotent.opposite_unipotent_closure m)

theorem suzukiIndex_goodSylowPrime (m : ℕ) (hm : 1 ≤ m) :
    CFSGReduction.GoodSylowPrime (CFSG.Index.Model (.suzuki m hm)) 2 :=
  goodSylowPrime m

end SymmetricSubgroupAsymptotics.CFSGSuzukiModelGoodSylow
