import SymmetricSubgroupAsymptotics.CFSGInvolutiveTwoGroupFixedIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientPositiveStability

/-! Disjoint conjugates of the actual exceptional-fixed positive group
force disjoint conjugates of the whole positive subgroup of the SAME
original F4 Model. The full intersection is an invariant finite 2-group;
no arbitrary fixed-point lift or ordinary F4 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDisjointModelPositive
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourAmbientPositiveStability
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalAmbientHom
open CFSGInvolutiveTwoGroupFixedIntersection

private instance modelFinite (m : ℕ) : Finite (Model CartanMatrix.F₄ (Field m)) :=
  Finite.of_injective (rawHom (Field m)) (rawHom_injective (Field m))

theorem model_positive_disjoint_of_fixed (m : ℕ) (g : originalModelFixed m)
    (hdisj : fixedPositive m⊓(fixedPositive m).map (MulAut.conj g).toMonoidHom=⊥) :
    modelPositive (Field m)⊓(modelPositive (Field m)).map
      (MulAut.conj g.val).toMonoidHom=⊥ := by
  have hP : IsPGroup 2 (modelPositive (Field m)) :=
    modelPositiveSylow_coe m ▸ (modelPositiveSylow m).isPGroup'
  have hstable (x : Model CartanMatrix.F₄ (Field m)) (hx : x∈modelPositive (Field m)) :
      reeAutomorphism m x∈modelPositive (Field m) := by
    have ht : reeAutomorphism m x∈(modelPositive (Field m)).map
        (reeAutomorphism m).toMonoidHom := ⟨x,hx,rfl⟩
    rw [ree_preserves_modelPositive] at ht
    exact ht
  have hd : (modelPositive (Field m)).comap (originalModelFixed m).subtype⊓
      ((modelPositive (Field m)).comap (originalModelFixed m).subtype).map
        (MulAut.conj g).toMonoidHom=⊥ := by
    rw [←fixedPositive_eq_model_comap]
    exact hdisj
  exact inf_conjugate_eq_bot_of_fixed (modelPositive (Field m)) (originalModelFixed m)
    hP (reeAutomorphism m).toMonoidHom (reeAutomorphism_involutive m) hstable
    (fun _=>Iff.rfl) g hd

end SymmetricSubgroupAsymptotics.CFSGReeFFourDisjointModelPositive
