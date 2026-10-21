import SymmetricSubgroupAsymptotics.BinaryBooleanFourRepresentationLeadingMiddle
import SymmetricSubgroupAsymptotics.BinaryBooleanFourCoefficientPrefix
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates
import SymmetricSubgroupAsymptotics.BooleanFourFullPrefixThreeGenerators
import SymmetricSubgroupAsymptotics.RepresentationLeadingPrefixDimension
import SymmetricSubgroupAsymptotics.BooleanFourRepresentationHeadFiveDimension

/-! A head-five actual submodule under the elementary Boolean action has
dimension at most twelve. The numeric coefficient prefix retains every
lower term; the full thirteen-dimensional endpoint needs only three
generators and is therefore excluded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
variable {G : Type} [Group G] [MulAction G (Fin 16)]

theorem boolean_four_translation_head_five_dimension_le_twelve
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin 16)))
    (e : Equiv.Perm (Fin 16)) (u : Fin 4 → G)
    (htranslation : ∀ (i : Fin 4) (x : Fin 16),
      e ((u i)⁻¹ • e.symm x)=flipIndex i x)
    (hcomm : ∀ (g : G) (i : Fin 4),Commute g (u i))
    (hhead : 5≤Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Module.finrank (ZMod 2) W.toSubmodule≤12 := by
  let rho := W.toRepresentation
  let P : V ≃ₗ[ZMod 2] V := (reindex e).trans coordinates
  let C : W.toSubmodule →ₗ[ZMod 2] V := P.toLinearMap.comp W.toSubmodule.subtype
  have hC : Function.Injective C := by
    intro v w he
    exact Subtype.ext (P.injective he)
  let q : G →* Equiv.Perm (Fin 16) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Fin 16))
  have hq (g : G) (x : Fin 16) : q g x=e (g • e.symm x) := rfl
  have hpoint (i : Fin 4) : q (u i)⁻¹=pointTranslation i := by
    apply Equiv.ext
    intro x
    exact htranslation i x
  have hcentral (g : G) (i : Fin 4) : Commute (q g⁻¹) (pointTranslation i) := by
    have h := ((hcomm g i).inv_inv).map q
    rwa [hpoint i] at h
  have hactual (g : G) (v : W.toSubmodule) :
      C (rho g v)=evaluate (fun x => evaluate (C v) (q g⁻¹ x)) := by
    change evaluate (fun x => v.val (g⁻¹ • e.symm x))=
      evaluate (fun x => evaluate (evaluate (fun j => v.val (e.symm j))) (q g⁻¹ x))
    rw [evaluate_involutive]
    congr 1
    funext x
    rw [hq,Equiv.symm_apply_apply]
  have hstable (g : G) (v : W.toSubmodule)
      (hv : ∀ j : Fin 16,13≤j.val → C v j=0) :
      ∀ j : Fin 16,13≤j.val → C (rho g v) j=0 := by
    apply (mem_prefixChart _).mp
    rw [hactual]
    exact centralizing_permutation_preserves_prefix (q g⁻¹) (hcentral g)
      (C v) ((mem_prefixChart _).mpr hv)
  have hdiff (i : Fin 4) (v : W.toSubmodule) :
      C (rho (u i) v-v)=derivative i (C v) := by
    change evaluate (fun x => v.val ((u i)⁻¹ • e.symm x)-v.val (e.symm x))=
      derivative i (evaluate (fun x => v.val (e.symm x)))
    rw [derivative_evaluate]
    have he : (fun x => v.val ((u i)⁻¹ • e.symm x)-v.val (e.symm x))=
        translate i (fun x => v.val (e.symm x))-(fun x => v.val (e.symm x)) := by
      funext x
      change v.val ((u i)⁻¹ • e.symm x)-v.val (e.symm x)=
        v.val (e.symm (flipIndex i x))-v.val (e.symm x)
      have hx : (u i)⁻¹ • e.symm x=e.symm (flipIndex i x) :=
        e.injective (by rw [Equiv.apply_symm_apply];exact htranslation i x)
      rw [hx]
    exact congrArg (fun f : V => evaluate f) he
  exact boolean_four_representation_head_five_dimension_le_twelve rho C hC
    (fun i => ⟨u i,hdiff i⟩) hstable hhead

end SymmetricSubgroupAsymptotics
