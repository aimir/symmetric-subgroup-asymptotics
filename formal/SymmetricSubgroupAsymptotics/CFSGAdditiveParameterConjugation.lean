import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! Conjugation identities for a finite additive parameter space can be
proved on the literal one-coordinate elements. This universal-property
step retains the actual ambient conjugator and every parameter relation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation
variable {J K G : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K] [Group G]

private theorem piMultiplicative_single (i : J) (a : Multiplicative K) :
    (MulEquiv.piMultiplicative (fun _:J=>K)).symm (Pi.mulSingle i a)=
      Multiplicative.ofAdd (Pi.single i a.toAdd) := by
  apply Multiplicative.toAdd.injective
  ext j
  by_cases hj : j=i
  · subst j
    change ((Pi.mulSingle i a : J→Multiplicative K) i).toAdd=(Pi.single i a.toAdd : J→K) i
    rw [Pi.mulSingle_eq_same,Pi.single_eq_same]
  · change ((Pi.mulSingle i a : J→Multiplicative K) j).toAdd=(Pi.single i a.toAdd : J→K) j
    rw [Pi.mulSingle_eq_of_ne hj,Pi.single_eq_of_ne hj]
    rfl

theorem hom_ext (f g : Multiplicative (J→K)→*G)
    (h : ∀i a,f (Multiplicative.ofAdd (Pi.single i a))=
      g (Multiplicative.ofAdd (Pi.single i a))) : f=g := by
  let e := MulEquiv.piMultiplicative (fun _:J=>K)
  have he : f.comp e.symm.toMonoidHom=g.comp e.symm.toMonoidHom := by
    apply MonoidHom.pi_ext
    intro i a
    change f (e.symm (Pi.mulSingle i a))=g (e.symm (Pi.mulSingle i a))
    rw [piMultiplicative_single, h i a.toAdd]
  apply MonoidHom.ext
  intro v
  have hv := DFunLike.congr_fun he (e v)
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using hv

theorem conjugation_of_single (psi : Multiplicative (J→K)→*G)
    (e : (J→K)≃+(J→K)) (g:G)
    (h : ∀i a,g*psi (Multiplicative.ofAdd (Pi.single i a))*g⁻¹=
      psi (Multiplicative.ofAdd (e (Pi.single i a)))) (v:J→K) :
    g*psi (Multiplicative.ofAdd v)*g⁻¹=psi (Multiplicative.ofAdd (e v)) := by
  let f := (MulAut.conj g).toMonoidHom.comp psi
  let q := psi.comp (AddEquiv.toMultiplicative e).toMonoidHom
  have he : f=q := hom_ext f q h
  exact DFunLike.congr_fun he (Multiplicative.ofAdd v)

section Field
variable [Field K]

omit [AddCommGroup K] in
theorem elementary_apply {i j:J} (hij:i≠j) (a:K) (v:J→K) :
    (CFSGTypeAElementaryMatrices.elementary hij a).toLin' v=v+Pi.single i (a*v j) := by
  change Matrix.mulVec (1+Matrix.single i j a) v=v+Pi.single i (a*v j)
  rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
  rfl

end Field
end SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation
