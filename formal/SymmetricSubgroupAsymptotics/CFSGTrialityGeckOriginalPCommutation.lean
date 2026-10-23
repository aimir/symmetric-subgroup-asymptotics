import SymmetricSubgroupAsymptotics.CFSGCentralKernelCommutation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeSylows
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPreimageProjection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageRawCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionPElementSeparation

/-! Commutation with an actual p-element in the SAME original triality
model lifts to its literal raw matrix representative. The two central
quotients are handled separately: the original projective projection,
then the actual matrix action. Their composite is not presumed central. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPCommutation
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalOppositeSylows CFSGTrialityGeckOriginalOrderLower
open CFSGTrialityGeckOriginalPreimageProjection CFSGTrialityGeckPreimageRawCoordinates
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckMatrixActionCentralKernel CFSGTrialityGeckActionPElementSeparation
open CFSGTrialityGeckFixedDerivedMatrixLift
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

private theorem p_element_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (p : ℕ) (x : G) (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    ∃ k : ℕ, (f x) ^ p ^ k = 1 := by
  obtain ⟨k,hk⟩ := hx
  exact ⟨k,(map_pow f x (p^k)).symm.trans
    ((congrArg f hk).trans (map_one f))⟩

theorem originalProjection_commute_iff (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (x y : DerivedImage q)
    (hx : ∃ k : ℕ, x ^ q.prime ^ k = 1) :
    Commute (originalProjection q x) (originalProjection q y) ↔ Commute x y :=
  CFSGCentralKernelCommutation.map_commute_iff (originalProjection q) (imagePositiveSylow q)
    (originalProjection_sylow_injective q) (originalProjection_kernel_le_center q) x y hx

def preimageMatrixHom (q : CFSG.PrimePower) :
    naturalDerivedPreimage q →* MatrixGroup (q.Extension 3) :=
  (FixedMatrixGroup q).subtype.comp (naturalDerivedPreimage q).subtype

theorem preimageMatrixHom_action (q : CFSG.PrimePower) (x : naturalDerivedPreimage q) :
    matrixAction (q.Extension 3) (preimageMatrixHom q x) = (preimageToImage q x).val := rfl

private theorem preimage_action_commute (q : CFSG.PrimePower)
    (x y : naturalDerivedPreimage q)
    (h : Commute (preimageToImage q x) (preimageToImage q y)) :
    Commute (matrixAction (q.Extension 3) (preimageMatrixHom q x))
      (matrixAction (q.Extension 3) (preimageMatrixHom q y)) := by
  exact congrArg (fun z : DerivedImage q => z.val) h.eq

private theorem preimage_matrix_commute (q : CFSG.PrimePower)
    (x y : naturalDerivedPreimage q) (hx : ∃ k : ℕ, x ^ q.prime ^ k = 1)
    (h : Commute (preimageToImage q x) (preimageToImage q y)) :
    Commute (preimageMatrixHom q x) (preimageMatrixHom q y) := by
  have hxm : ∃ k : ℕ, (preimageMatrixHom q x) ^ q.prime ^ k = 1 :=
    p_element_map (preimageMatrixHom q) q.prime x hx
  exact CFSGCentralKernelCommutation.commute_of_map_commute
    (matrixAction (q.Extension 3)) (CFSGTrialityGeckAmbientPositiveSylow.ambientPositiveSylow
      (q.Extension 3) q.prime) (ambientSylow_action_injective (q.Extension 3) q.prime)
    (matrixAction_kernel_le_center (q.Extension 3)) _ _ hxm (preimage_action_commute q x y h)

theorem originalPreimage_raw_commute (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (x y : naturalDerivedPreimage q)
    (hx : ∃ k : ℕ, x ^ q.prime ^ k = 1)
    (hxy : Commute (originalPreimageProjection q x) (originalPreimageProjection q y)) :
    Commute (preimageRawInclusion q x) (preimageRawInclusion q y) := by
  have hxi : ∃ k : ℕ, (preimageToImage q x) ^ q.prime ^ k = 1 :=
    p_element_map (preimageToImage q) q.prime x hx
  have hi : Commute (preimageToImage q x) (preimageToImage q y) :=
    (originalProjection_commute_iff q _ _ hxi).mp hxy
  exact congrArg (fun z : MatrixGroup (q.Extension 3) => z.val)
    (preimage_matrix_commute q x y hx hi).eq

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPCommutation
