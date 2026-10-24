import SymmetricSubgroupAsymptotics.CFSGFFourOriginalExceptionalModel
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldParameters
import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram

/-! The prescribed ORIGINAL ReeF4 root powers form an actual involutive
automorphism of the SAME original F4 Model. The exceptional automorphism
is composed with the literal defining-field Frobenius power. This applies
also to m=0, without assuming ordinary F4 simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalAutomorphism
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
open CFSGReeFFourFieldParameters CFSGFFourOriginalExceptionalModel
local notation "A"=>CartanMatrix.F₄

private def betaModel (m:ℕ):MulAut (Model A (Field m)):=
  CFSGSerreFieldDiagram.modelAutomorphism A (Field m) (Equiv.refl (Fin 4))
    (fun _ _=>rfl) (alphaEquiv m).symm

private theorem betaModel_root (m:ℕ) (neg:Bool) (i:Fin 4) (t:Field m):
    betaModel m (modelRoot A (Field m) neg i t)=modelRoot A (Field m) neg i (beta m t):=by
  apply Subtype.ext
  change CFSGSerreFieldDiagram.ambientAutomorphism A (Field m) (Equiv.refl (Fin 4))
    (fun _ _=>rfl) (alphaEquiv m).symm (rootEquiv A (Field m) neg i t)=
      rootEquiv A (Field m) neg i (beta m t)
  apply LinearEquiv.toLinearMap_injective
  exact CFSGSerreFieldDiagram.ambientAutomorphism_isRootElement A (Field m)
    (Equiv.refl (Fin 4)) (fun _ _=>rfl) (alphaEquiv m).symm neg i t _
    (rootEquiv_isRootElement A (Field m) neg i t)

def reeAutomorphism (m:ℕ):MulAut (Model A (Field m)):=
  (betaModel m).trans (exceptionalModelEquiv (Field m))

theorem reeAutomorphism_root (m:ℕ) (neg:Bool) (i:Fin 4) (t:Field m):
    reeAutomorphism m (modelRoot A (Field m) neg i t)=
      modelRoot A (Field m) neg (CFSG.Models.reverseNode i) (t^(originalExponent m i)):=by
  change exceptionalModelEquiv (Field m) (betaModel m (modelRoot A (Field m) neg i t))=_
  rw [betaModel_root,exceptionalModelEquiv_root]
  fin_cases i
  · change modelRoot A (Field m) neg 3 ((beta m t)^2)=
      modelRoot A (Field m) neg 3 (t^(2^(m+1)))
    rw [←alpha_eq_beta_square]
    rfl
  · change modelRoot A (Field m) neg 2 ((beta m t)^2)=
      modelRoot A (Field m) neg 2 (t^(2^(m+1)))
    rw [←alpha_eq_beta_square]
    rfl
  · rfl
  · rfl

theorem reeAutomorphism_involutive (m:ℕ):Function.Involutive (reeAutomorphism m):=by
  have he:(reeAutomorphism m).toMonoidHom.comp (reeAutomorphism m).toMonoidHom=
      MonoidHom.id (Model A (Field m)):=by
    apply MonoidHom.eq_of_eqOn_dense (rootSet_generate A (Field m))
    rintro g ⟨neg,i,t,rfl⟩
    change reeAutomorphism m (reeAutomorphism m (modelRoot A (Field m) neg i t))=_
    rw [reeAutomorphism_root,reeAutomorphism_root,original_parameter_power_twice]
    simp only [CFSG.Models.reverseNode,Fin.rev_rev]
    rfl
  intro g
  exact congrArg (fun f:Model A (Field m)→*Model A (Field m)=>f g) he

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalAutomorphism
