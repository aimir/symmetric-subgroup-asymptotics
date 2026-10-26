import SymmetricSubgroupAsymptotics.TernaryWreathAffineSemidirectEquiv
import SymmetricSubgroupAsymptotics.AbelianSemidirectPlaneKernelClassBound
import SymmetricSubgroupAsymptotics.FinitePGroupProperSubgroupCardinality
import Mathlib.Algebra.Module.ZMod

/-! The literal translation intersection of a ternary affine subgroup
is an F3 submodule invariant under its OWN projected signed subgroup.
A proper intersection has at most 27 elements. No unsigned invariance
or splitting of the subgroup is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourAffineKernelCoordinates
open TernaryWreathAffineSemidirectEquiv TernarySignedWreathLinearEquiv

abbrev Translation := Multiplicative (Fin 4 → ZMod 3)

local instance : Finite (Affine (Fin 4)) :=
  Finite.of_equiv (Translation × Model (Fin 4)) SemidirectProduct.equivProd.symm

def projection (L : Subgroup (Affine (Fin 4))) : L →* Model (Fin 4) :=
  (SemidirectProduct.rightHom : Affine (Fin 4) →* Model (Fin 4)).comp L.subtype

def translationSubmodule (L : Subgroup (Affine (Fin 4))) :
    Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
  AddSubgroup.toZModSubmodule 3
    (L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))).toAddSubgroup'

def translationEquiv (L : Subgroup (Affine (Fin 4))) :
    (L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))) ≃
      translationSubmodule L where
  toFun n := ⟨n.val.toAdd,n.property⟩
  invFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem projected_preserves_submodule (L : Subgroup (Affine (Fin 4)))
    (g : (projection L).range) (v : Fin 4 → ZMod 3)
    (hv : v∈translationSubmodule L) :
    linearHom (Fin 4) g.val v∈translationSubmodule L := by
  have h := (AbelianSemidirectPlaneKernelClassBound.projected_preserves_intersection
    (translationAction (Fin 4)) L g (Multiplicative.ofAdd v)).mpr hv
  exact h

theorem translation_card_le_twentySeven (L : Subgroup (Affine (Fin 4)))
    (hproper : translationSubmodule L≠⊤) :
    Nat.card (L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4)))≤27 := by
  let K := L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))
  have hK : K≠⊤ := by
    intro he
    apply hproper
    ext v
    change Multiplicative.ofAdd v∈K ↔ True
    simp only [he,Subgroup.mem_top]
  have hcard : Nat.card Translation=3^4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Translation ≃ (Fin 4 → ZMod 3)),
      Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have h := FinitePGroupProperSubgroupCardinality.prime_mul_card_le 3
    (IsPGroup.of_card hcard) K hK
  rw [hcard] at h
  change Nat.card K≤27
  omega

end SymmetricSubgroupAsymptotics.TernaryFourAffineKernelCoordinates
