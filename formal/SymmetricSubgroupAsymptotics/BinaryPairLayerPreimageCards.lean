import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerCoordinates
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation
import SymmetricSubgroupAsymptotics.PermutationCoordinateSumApply

/-! Exact cardinalities of the SAME pair-sum preimage and pair-constant
image. The reversible original coordinates preserve both layers and
their correlation; no independently chosen group action is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance layerPreimageCardsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

def pairSumPreimageEquiv (A : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    A.comap F.pairSum ≃ (Fin w → ZMod 2) × A where
  toFun v := (F.pairZeroRestriction v.val,⟨F.pairSum v.val,v.property⟩)
  invFun v := ⟨F.pairLayerCoordinateEquiv.symm (v.1,v.2.val),by
    change F.pairSum (F.pairLayerCoordinateEquiv.symm (v.1,v.2.val)) ∈ A
    have he := congrArg Prod.snd (F.pairLayerCoordinateEquiv.apply_symm_apply (v.1,v.2.val))
    change F.pairSum (F.pairLayerCoordinateEquiv.symm (v.1,v.2.val))=v.2.val at he
    rw [he]
    exact v.2.property⟩
  left_inv v := Subtype.ext (F.pairLayerCoordinateEquiv.symm_apply_apply v.val)
  right_inv v := by
    have he := F.pairLayerCoordinateEquiv.apply_symm_apply (v.1,v.2.val)
    apply Prod.ext
    · change F.pairZeroRestriction (F.pairLayerCoordinateEquiv.symm (v.1,v.2.val))=v.1
      exact congrArg (fun a : (Fin w → ZMod 2) × (Fin w → ZMod 2) => a.1) he
    · apply Subtype.ext
      change F.pairSum (F.pairLayerCoordinateEquiv.symm (v.1,v.2.val))=v.2.val
      exact congrArg (fun a : (Fin w → ZMod 2) × (Fin w → ZMod 2) => a.2) he

omit [Finite X] in
theorem pairSum_preimage_card (A : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Nat.card (A.comap F.pairSum)=2^w*Nat.card A := by
  rw [Nat.card_congr (F.pairSumPreimageEquiv A),Nat.card_prod]
  simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]

def pairConstantImageEquiv (A : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    A ≃ A.map F.pairConstant :=
  Equiv.ofBijective (fun a => ⟨F.pairConstant a.val,⟨a.val,a.property,rfl⟩⟩) (by
    constructor
    · intro a b he
      exact Subtype.ext (F.pairConstant_injective (congrArg Subtype.val he))
    · rintro ⟨v,a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩)

omit [Finite X] in
theorem pairConstant_image_card (A : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Nat.card (A.map F.pairConstant)=Nat.card A :=
  (Nat.card_congr (F.pairConstantImageEquiv A)).symm

theorem coordinateSum_eq_pairSum (v : X → ZMod 2) :
    PermutationAugmentation.coordinateSum (ZMod 2) X v=
      PermutationAugmentation.coordinateSum (ZMod 2) (Fin w) (F.pairSum v) := by
  have htwo : (Finset.univ : Finset (ZMod 2))={0,1} := by
    ext b
    fin_cases b <;> simp
  rw [permutation_coordinateSum_apply,permutation_coordinateSum_apply]
  rw [←Equiv.sum_comp F.frame v,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [htwo,Finset.sum_pair (by decide : (0 : ZMod 2)≠1)]
  rfl

theorem pairSum_preimage_le_augmentation
    (A : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hA : A≤PermutationAugmentation.space (ZMod 2) (Fin w)) :
    A.comap F.pairSum≤PermutationAugmentation.space (ZMod 2) X := by
  intro v hv
  change PermutationAugmentation.coordinateSum (ZMod 2) X v=0
  rw [F.coordinateSum_eq_pairSum]
  exact hA hv

end SymmetricSubgroupAsymptotics.BinaryPairFrame
