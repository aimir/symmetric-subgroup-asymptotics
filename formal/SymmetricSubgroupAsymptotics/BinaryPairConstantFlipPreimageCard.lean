import SymmetricSubgroupAsymptotics.BinaryPairIntervalPreimageGeometry

/-! The selected constant-flip preimage count for an arbitrary actual
upper subspace S. Its lower denominator is A≤S, so no augmentation or
literal finite model is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance constantFlipPreimageCardPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem constant_flip_fixed_preimage_card
    (A S : Submodule (ZMod 2) (Fin w → ZMod 2)) (hAS : A≤S)
    (z : F.top.ker) (hz : F.bits z=(fun _ => 1)) :
    Nat.card {v : X → ZMod 2 // v∈S.comap F.pairSum ∧
      permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant}=
      2^w*Nat.card A := by
  have hiff (v : X → ZMod 2) :
      (v∈S.comap F.pairSum ∧
        permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant) ↔
      v∈A.comap F.pairSum := by
    rw [F.constant_flip_displacement z hz]
    constructor
    · rintro ⟨_,a,ha,he⟩
      change F.pairSum v∈A
      rw [←F.pairConstant_injective he]
      exact ha
    · intro hv
      exact ⟨hAS hv,⟨F.pairSum v,hv,rfl⟩⟩
  let e : {v : X → ZMod 2 // v∈S.comap F.pairSum ∧
      permutationFunctionRepresentation (ZMod 2) U X z.val v-v∈A.map F.pairConstant} ≃
      A.comap F.pairSum := {
    toFun v := ⟨v.val,(hiff v.val).mp v.property⟩
    invFun v := ⟨v.val,(hiff v.val).mpr v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (F.pairSum_preimage_card A)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
