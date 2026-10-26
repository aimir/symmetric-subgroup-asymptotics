import SymmetricSubgroupAsymptotics.OddMarkerAffineSemidirectEquiv
import SymmetricSubgroupAsymptotics.TernarySignedWreathLinearEquiv
import SymmetricSubgroupAsymptotics.PermutationalWreathAffineCoordinates
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Exact ternary affine coordinates on any original S3 wreath product.
The existing general affine-wreath equivalence is reused; only the local
S3 chart and the harmless pointwise multiplicative tag are transported.
The rightmost permutation remains the original one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryWreathAffineSemidirectEquiv
open OddMarkerAffineSemidirectEquiv

variable (I : Type)

abbrev Wreath := PermutationalWreathProduct OddMarkerGroup (Equiv.Perm I) I

def translationEquiv : (I → C3) ≃* Multiplicative (I → ZMod 3) where
  toFun v := Multiplicative.ofAdd (fun i => (v i).toAdd)
  invFun v := fun i => Multiplicative.ofAdd (v.toAdd i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def translationAction : TernarySignedWreathLinearEquiv.Model I →*
    MulAut (Multiplicative (I → ZMod 3)) :=
  LinearSemidirectCoprimeSocleBounds.linearAction (TernarySignedWreathLinearEquiv.linearHom I)

abbrev Affine := Multiplicative (I → ZMod 3) ⋊[translationAction I]
  TernarySignedWreathLinearEquiv.Model I

private def baseEquiv : Wreath I ≃*
    PermutationalWreathProduct OddMarkerAffineSemidirectEquiv.Model (Equiv.Perm I) I := by
  let f : Wreath I →* PermutationalWreathProduct
      OddMarkerAffineSemidirectEquiv.Model (Equiv.Perm I) I :=
    PermutationalWreathProduct.mapBase OddMarkerAffineSemidirectEquiv.equiv.toMonoidHom
  apply MulEquiv.ofBijective f
  constructor
  · intro g h he
    apply PermutationalWreathProduct.ext
    · funext i
      apply OddMarkerAffineSemidirectEquiv.equiv.injective
      exact congrArg (fun z => z.left i) he
    · exact congrArg (fun z : PermutationalWreathProduct
        OddMarkerAffineSemidirectEquiv.Model (Equiv.Perm I) I => z.right) he
  · intro w
    refine ⟨⟨fun i => OddMarkerAffineSemidirectEquiv.equiv.symm (w.left i),w.right⟩,?_⟩
    apply PermutationalWreathProduct.ext
    · funext i
      exact OddMarkerAffineSemidirectEquiv.equiv.apply_symm_apply (w.left i)
    · rfl

private def tagEquiv : PermutationalWreathAffineCoordinates.Model
    (R:=Equiv.Perm I) (I:=I) scalarAction ≃* Affine I :=
  SemidirectProduct.congr (translationEquiv I)
    (MulEquiv.refl (TernarySignedWreathLinearEquiv.Model I)) (fun g => by
      apply MulEquiv.ext
      intro v
      rfl)

def equiv : Wreath I ≃* Affine I :=
  (baseEquiv I).trans
    ((PermutationalWreathAffineCoordinates.equiv (R:=Equiv.Perm I) (I:=I) scalarAction).symm.trans
      (tagEquiv I))

theorem equiv_preserves_original_top (w : Wreath I) :
    (equiv I w).right.right=w.right := by
  let e := PermutationalWreathAffineCoordinates.equiv (R:=Equiv.Perm I) (I:=I) scalarAction
  have h := congrArg PermutationalWreathProduct.right (e.apply_symm_apply (baseEquiv I w))
  have htop : (e.symm (baseEquiv I w)).right.right=(baseEquiv I w).right := by
    change (e.symm (baseEquiv I w)).right.right=(baseEquiv I w).right at h
    exact h
  change (e.symm (baseEquiv I w)).right.right=w.right
  exact htop.trans rfl

end SymmetricSubgroupAsymptotics.TernaryWreathAffineSemidirectEquiv
