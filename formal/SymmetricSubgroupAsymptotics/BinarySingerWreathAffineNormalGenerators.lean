import SymmetricSubgroupAsymptotics.WreathAffineCoordinates
import SymmetricSubgroupAsymptotics.C2WreathGeneration
import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles

/-! Independent local Singer factors and the actual block swap force the
whole binary translation pair to be the unique minimal normal subgroup.
Any positive normal-generator bound on the retained complement then lifts
unchanged. This covers the translation geometry shared by rows8 and9. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinarySingerWreathAffineNormalGenerators

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev V := Multiplicative Vector

variable (A : Subgroup LinearGroup) (hsinger : singer ∈ A)

def localInclusion : Row18.linearGroup →* A :=
  Subgroup.inclusion (by
    rw [Row18.linearGroup_eq_zpowers]
    exact Subgroup.zpowers_le.mpr hsinger)

def singerElement : A := ⟨singer, hsinger⟩

variable (C : Subgroup (C2Wreath.W A))
  (hfirst : C2Wreath.firstFactor (singerElement A hsinger) ∈ C)
  (hswap : (inr C2Wreath.gen : C2Wreath.W A) ∈ C)

include hfirst in
theorem first_mem (r : Row18.linearGroup) :
    C2Wreath.firstFactor (localInclusion A hsinger r) ∈ C := by
  have hr : r.val ∈ Subgroup.zpowers singer := by
    rw [← Row18.linearGroup_eq_zpowers]
    exact r.property
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hr
  have heq : singerElement A hsinger ^ z = localInclusion A hsinger r := Subtype.ext hz
  rw [← heq, map_zpow]
  exact C.zpow_mem hfirst z

def localLift (r : Row18.linearGroup) : C :=
  ⟨C2Wreath.firstFactor (localInclusion A hsinger r), first_mem A hsinger C hfirst r⟩

private theorem singer_polynomial_zero (v : V) :
    Multiplicative.ofAdd ((singer ^ 4) v.toAdd) *
      Multiplicative.ofAdd ((singer ^ 2) v.toAdd) * Multiplicative.ofAdd (singer v.toAdd) = 1 := by
  revert v
  decide +kernel

include hfirst hswap in
theorem irreducible : IrreducibleAbelianSemidirect.Irreducible
    (WreathAffineCoordinates.restrictedAction (AffineModel.linAut A) C) := by
  let s : C := ⟨C2Wreath.firstFactor (singerElement A hsinger), hfirst⟩
  let b : C := ⟨inr C2Wreath.gen, hswap⟩
  apply twoBlock_irreducible_of_projection (AffineModel.linAut Row18.linearGroup)
    (WreathAffineCoordinates.restrictedAction (AffineModel.linAut A) C)
    (BinaryDiagonalSwap.affine_irreducible Row18.linearGroup Row18.irreducible)
    (localLift A hsinger C hfirst) ?_ b ?_ s ?_
  · intro r v
    change WreathAffineCoordinates.action (AffineModel.linAut A)
      (inl (localInclusion A hsinger r, 1)) (v, 1) = _
    rw [WreathAffineCoordinates.action_inl, map_one]
    rfl
  · intro v
    change WreathAffineCoordinates.action (AffineModel.linAut A)
      (⟨(1, 1), C2Wreath.gen⟩ : C2Wreath.W A) v = _
    rw [WreathAffineCoordinates.action_swap, map_one]
    rfl
  · intro v
    have hp (n : ℕ) : ((s ^ n : C) : C2Wreath.W A) =
        C2Wreath.firstFactor (singerElement A hsinger ^ n) := by
      change C2Wreath.firstFactor (singerElement A hsinger) ^ n = _
      exact (map_pow C2Wreath.firstFactor _ n).symm
    have ha (n : ℕ) :
        WreathAffineCoordinates.restrictedAction (AffineModel.linAut A) C (s ^ n) v =
          (Multiplicative.ofAdd ((singer ^ n) v.1.toAdd), v.2) := by
      simp only [WreathAffineCoordinates.restrictedAction, MonoidHom.comp_apply]
      change WreathAffineCoordinates.action (AffineModel.linAut A)
        ((s ^ n : C) : C2Wreath.W A) v = _
      rw [hp n]
      change WreathAffineCoordinates.action (AffineModel.linAut A)
        (inl (singerElement A hsinger ^ n, 1)) v = _
      rw [WreathAffineCoordinates.action_inl, map_one]
      rfl
    have haone := ha 1
    simp only [pow_one] at haone
    rw [ha 4, ha 2, haone]
    apply Prod.ext
    · exact singer_polynomial_zero v.1
    · change v.2 * v.2 * v.2 = v.2
      rw [BinaryDiagonalSwap.affine_translation_binary, one_mul]

include hfirst hswap in
theorem normal_generating_tuples {t : ℕ} (ht : 0 < t)
    (hC : ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin t → C, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (WreathAffineCoordinates.Model (AffineModel.linAut A) C), N.Normal →
      ∃ x : Fin t → WreathAffineCoordinates.Model (AffineModel.linAut A) C,
        Subgroup.normalClosure (Set.range x) = N :=
  IrreducibleAbelianSemidirect.normal_generating_tuples
    (WreathAffineCoordinates.restrictedAction (AffineModel.linAut A) C)
    ((WreathAffineCoordinates.action_injective (AffineModel.linAut A)
      (BinaryDiagonalSwap.affine_linAut_injective A)).comp Subtype.val_injective)
    (irreducible A hsinger C hfirst hswap) ht hC

end BinarySingerWreathAffineNormalGenerators
end SymmetricSubgroupAsymptotics

end
