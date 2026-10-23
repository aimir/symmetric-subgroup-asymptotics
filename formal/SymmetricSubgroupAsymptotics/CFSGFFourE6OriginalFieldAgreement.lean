import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFieldAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedEndFields

/-! The actual original middle commutator couples the two end A2 fields.
Its coefficient-one second factor gives field agreement at a=1, also
in characteristic two. All signed native charts share one field map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFieldAgreement
open CFSGFFourE6OriginalMiddleFieldAction CFSGFFourE6OriginalMiddleFactors
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6OriginalSignedEndFields
open CFSG.Models.Chevalley

theorem fields_agree (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K)) (tau kap : RingAut K) (d e : Kˣ)
    (hpair : ∀a,f (originalSimpleHom K false 1 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 1 (Multiplicative.ofAdd ((d : K)*tau a)))
    (hpairneg : ∀a,f (originalSimpleHom K true 1 (Multiplicative.ofAdd a))=
      originalSimpleHom K true 1 (Multiplicative.ofAdd ((d : K)⁻¹*tau a)))
    (hsingle : ∀a,f (originalSimpleHom K false 2 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 2 (Multiplicative.ofAdd ((e : K)*kap a)))
    (hsingleneg : ∀a,f (originalSimpleHom K true 2 (Multiplicative.ofAdd a))=
      originalSimpleHom K true 2 (Multiplicative.ofAdd ((e : K)⁻¹*kap a))) (b : K) : tau b=kap b := by
  have hR := middleLong_image K f tau kap d e hpair hpairneg hsingle
  have hS := middleShort_image K f tau kap d e hpair hsingle hsingleneg
  have he := congrArg f (original_middle_commutator K (1 : K) b)
  rw [map_commutatorElement,hpair,hsingle,map_one tau,mul_one] at he
  rw [map_mul f,hR,hS,original_middle_commutator] at he
  have hp := original_middleFactor_snd_eq K p _ _ _ _ he
  simp only [one_mul,map_neg,mul_neg] at hp
  have hc : (d : K)*((e : K)*kap b)=((e : K)*(d : K))*tau b := neg_inj.mp hp
  apply mul_left_cancel₀ (mul_ne_zero e.ne_zero d.ne_zero)
  calc
    _=(d : K)*((e : K)*kap b) := hc.symm
    _=_ := by ring

theorem exists_common_field_parameters (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀neg i,(originalSimpleHom K neg i).range.map f.toMonoidHom=(originalSimpleHom K neg i).range) :
    ∃(tau : RingAut K) (c : Fin 4→Kˣ),∀neg i a,
      f (originalSimpleHom K neg i (Multiplicative.ofAdd a))=
        originalSimpleHom K neg i (Multiplicative.ofAdd
          ((if neg then ((c i : K)⁻¹) else (c i : K))*tau a)) := by
  obtain ⟨tau,c,d,hc,hd,hpair⟩ := paired_signed_parameters_common_field K p f hfix
  obtain ⟨kap,e,h,he,hh,hsingle⟩ := singleton_signed_parameters_common_field K p f hfix
  have hagree : tau=kap := RingEquiv.ext (fields_agree K p f tau kap (Units.mk0 d hd) (Units.mk0 e he)
    (fun a=>(hpair a).2.1) (fun a=>(hpair a).2.2.2)
    (fun a=>(hsingle a).1) (fun a=>(hsingle a).2.2.1))
  cases hagree
  refine ⟨tau,![Units.mk0 c hc,Units.mk0 d hd,Units.mk0 e he,Units.mk0 h hh],?_⟩
  intro neg i a
  cases neg <;> fin_cases i
  · exact (hpair a).1
  · exact (hpair a).2.1
  · exact (hsingle a).1
  · exact (hsingle a).2.1
  · exact (hpair a).2.2.1
  · exact (hpair a).2.2.2
  · exact (hsingle a).2.2.1
  · exact (hsingle a).2.2.2

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFieldAgreement
