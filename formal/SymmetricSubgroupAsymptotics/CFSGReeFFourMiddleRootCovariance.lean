import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalAutomorphism

/-! Actual exceptional covariance of the original middle B2 Weyl/root
words. The two higher words swap with the literal beta/alpha powers.
No whole fixed-positive-group or derived-quotient claim occurs here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
local notation "A"=>CartanMatrix.F₄

theorem ree_weyl (m:ℕ) (i:Fin 4):
    reeAutomorphism m (weyl (Field m) i)=weyl (Field m) (CFSG.Models.reverseNode i):=by
  simp only [weyl,map_mul,reeAutomorphism_root,CharTwo.neg_eq,one_pow]

theorem middleLong_twist (m:ℕ) (t:Field m):
    reeAutomorphism m (middleLong (Field m) t)=middleShort (Field m) (beta m t):=by
  simp only [middleLong,map_mul,map_inv,ree_weyl,reeAutomorphism_root]
  rfl

theorem middleShort_twist (m:ℕ) (t:Field m):
    reeAutomorphism m (middleShort (Field m) t)=middleLong (Field m) (alpha m t):=by
  simp only [middleShort,map_mul,map_inv,ree_weyl,reeAutomorphism_root]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance
