import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalModel
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFieldParameters
import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram

/-! The prescribed ORIGINAL ReeG2 root powers are an actual involutive
model automorphism. The exceptional G2 quotient action is composed with
the actual field-tensor beta automorphism. The resulting root formulas
use exactly reverseNode and originalExponent from the original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalAutomorphism
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
open CFSGReeGTwoFieldParameters CFSGGTwoOriginalExceptionalModel
local notation "A" => CartanMatrix.G₂

private def betaModel (m : ℕ) : MulAut (Model A (Field m)) :=
  CFSGSerreFieldDiagram.modelAutomorphism A (Field m) (Equiv.refl (Fin 2))
    (fun _ _ => rfl) (alphaEquiv m).symm

private theorem betaModel_root (m : ℕ) (neg : Bool) (i : Fin 2) (t : Field m) :
    betaModel m (modelRoot A (Field m) neg i t)=
      modelRoot A (Field m) neg i (beta m t) := by
  apply Subtype.ext
  change CFSGSerreFieldDiagram.ambientAutomorphism A (Field m) (Equiv.refl (Fin 2))
      (fun _ _ => rfl) (alphaEquiv m).symm (rootEquiv A (Field m) neg i t)=
    rootEquiv A (Field m) neg i (beta m t)
  apply LinearEquiv.toLinearMap_injective
  exact CFSGSerreFieldDiagram.ambientAutomorphism_isRootElement A (Field m)
    (Equiv.refl (Fin 2)) (fun _ _ => rfl) (alphaEquiv m).symm neg i t _
    (rootEquiv_isRootElement A (Field m) neg i t)

def reeAutomorphism (m : ℕ) : MulAut (Model A (Field m)) :=
  (betaModel m).trans (exceptionalModelEquiv (Field m))

theorem reeAutomorphism_root (m : ℕ) (neg : Bool) (i : Fin 2) (t : Field m) :
    reeAutomorphism m (modelRoot A (Field m) neg i t)=
      modelRoot A (Field m) neg (CFSG.Models.reverseNode i) (t^(originalExponent m i)) := by
  change exceptionalModelEquiv (Field m) (betaModel m (modelRoot A (Field m) neg i t))=_
  rw [betaModel_root,exceptionalModelEquiv_root]
  fin_cases i
  · change modelRoot A (Field m) neg 1 ((beta m t)^3)=
      modelRoot A (Field m) neg 1 (t^(3^(m+1)))
    rw [←alpha_eq_beta_cube]
    rfl
  · rfl

theorem reeAutomorphism_involutive (m : ℕ) : Function.Involutive (reeAutomorphism m) := by
  have he : (reeAutomorphism m).toMonoidHom.comp (reeAutomorphism m).toMonoidHom=
      MonoidHom.id (Model A (Field m)) := by
    apply MonoidHom.eq_of_eqOn_dense (rootSet_generate A (Field m))
    rintro g ⟨neg,i,t,rfl⟩
    change reeAutomorphism m (reeAutomorphism m (modelRoot A (Field m) neg i t))=_
    rw [reeAutomorphism_root,reeAutomorphism_root,original_parameter_power_twice]
    simp only [CFSG.Models.reverseNode,Fin.rev_rev]
    rfl
  intro g
  exact congrArg (fun f : Model A (Field m) →* Model A (Field m) => f g) he

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalAutomorphism
