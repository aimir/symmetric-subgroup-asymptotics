import SymmetricSubgroupAsymptotics.CFSGTwistedDModelImageCovariance
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2

/-! Every element of the ORIGINAL graph-fixed group, and of its actual
derived subgroup, has image commuting with the actual semilinear natural
image twist. This is an unconditional original-carrier statement; it
does not assert a fixed literal natural matrix lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedImageTwist
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices CFSGSerreDiagram
open CFSGSerreOrdinaryTwists CFSGTwistedDFixedA2 CFSGTwistedDImageTwist

theorem fixed_model_fixed (s : ℕ) (q : CFSG.PrimePower) (g : Fixed s q) :
    CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D (s + 4)) (q.Extension 2)
      (dPermutation (s + 4)) (d_preserves (s + 4)) (definingFieldAutomorphism q 2)
      (toModel s q g) = toModel s q g := by
  apply Subtype.ext
  change typeDAmbientAction (s + 4) q g.val = g.val
  exact ((typeD_mem_twistGraph_iff (s + 4) q (g.val, g.val)).mp g.property.2).2.symm

theorem fixed_image_commutes (s : ℕ) (q : CFSG.PrimePower) (g : Fixed s q)
    (y : (orthogonalBaseChange (q.Extension 2) (s + 4) (by omega)).range) :
    orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega) (toModel s q g)
      (rangeTwist (q.Extension 2) s (definingFieldAutomorphism q 2) y) =
    rangeTwist (q.Extension 2) s (definingFieldAutomorphism q 2)
      (orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega) (toModel s q g) y) :=
  CFSGTwistedDModelImageCovariance.fixed_image_commutes (q.Extension 2) s
    (definingFieldAutomorphism q 2) (toModel s q g) (fixed_model_fixed s q g) y

theorem derived_image_commutes (s : ℕ) (q : CFSG.PrimePower) (g : Derived s q)
    (y : (orthogonalBaseChange (q.Extension 2) (s + 4) (by omega)).range) :
    orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega) (derivedToOriginal s q g)
      (rangeTwist (q.Extension 2) s (definingFieldAutomorphism q 2) y) =
    rangeTwist (q.Extension 2) s (definingFieldAutomorphism q 2)
      (orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega) (derivedToOriginal s q g) y) :=
  fixed_image_commutes s q g.val y

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedImageTwist
