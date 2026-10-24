import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstPairTailEquiv

/-! The SAME actual first-hyperbolic-pair stabilizer supplies a
literal copy of the smaller elementary symplectic group. Its action on
vectors extended by zero is exactly the smaller natural matrix action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformTail

open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

def tailHom (m : ℕ) : elementaryRootGroup K m →* elementaryRootGroup K (m + 1) :=
  (Subgroup.inclusion (show firstPairElementary K m ≤ elementaryRootGroup K (m + 1) from
    fun _ hu => hu.1)).comp (firstPairTailEquiv K m).symm.toMonoidHom

theorem tailHom_fixes_firstPair (m : ℕ) (A : elementaryRootGroup K m) :
    FixesFirstPair m ((tailHom K m A).val : Mat K (m + 1)) :=
  ((firstPairTailEquiv K m).symm A).property.2

theorem tailHom_tailMatrix (m : ℕ) (A : elementaryRootGroup K m) :
    tailMatrix m ((tailHom K m A).val : Mat K (m + 1)) = (A.val : Mat K m) := by
  have hh : firstPairTailToElementary K m ((firstPairTailEquiv K m).symm A) = A :=
    (firstPairTailEquiv K m).apply_symm_apply A
  exact congrArg (fun g : elementaryRootGroup K m => (g.val : Mat K m)) hh

theorem tailHom_tailExtend (m : ℕ) (A : elementaryRootGroup K m) (v : Index m → K) :
    ((tailHom K m A).val : Mat K (m + 1)) *ᵥ tailExtend m v =
      tailExtend m ((A.val : Mat K m) *ᵥ v) := by
  let T := tailHom K m A
  have hfix : FixesFirstPair m (T.val : Mat K (m + 1)) := tailHom_fixes_firstPair K m A
  have hpos : ((T.val : Mat K (m + 1)) *ᵥ tailExtend m v) (Sum.inl 0) = 0 := by
    have h := elementary_preserves_pairing (m + 1) T (tailExtend m v) (Pi.single (Sum.inr 0) 1)
    rw [hfix.2, pairing_neg_basis, pairing_neg_basis] at h
    exact h.trans (tailExtend_pos_zero m v)
  have hneg : ((T.val : Mat K (m + 1)) *ᵥ tailExtend m v) (Sum.inr 0) = 0 := by
    have h := elementary_preserves_pairing (m + 1) T (tailExtend m v) (Pi.single (Sum.inl 0) 1)
    rw [hfix.1, pairing_pos_basis, pairing_pos_basis] at h
    exact (neg_injective h).trans (tailExtend_neg_zero m v)
  have ht := tailMatrix_mulVec m (T.val : Mat K (m + 1)) v
  rw [show tailMatrix m (T.val : Mat K (m + 1)) = (A.val : Mat K m) from
    tailHom_tailMatrix K m A] at ht
  funext i
  rcases index_head_or_tail m i with rfl | rfl | ⟨j, rfl⟩
  · exact hpos.trans (tailExtend_pos_zero m _).symm
  · exact hneg.trans (tailExtend_neg_zero m _).symm
  · rw [tailExtend_tail]
    exact (congrFun ht j).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformTail
