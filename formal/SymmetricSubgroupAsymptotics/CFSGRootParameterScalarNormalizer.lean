import SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
import Mathlib.Algebra.Group.Subgroup.Finite

/-! A genuine group automorphism preserving an actual scalar-acting
subgroup normalizes the corresponding field-scalar action on an
injective additive root parameter. Both the scalar upper action and
realization of every scalar remain explicit model obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRootParameterScalarNormalizer
open CFSGRootParameterAutomorphism CFSGFiniteFieldScalarNormalizer
variable {K G : Type*} [Field K] [Finite K] [Group G]

theorem parameterAut_mem_scalar_normalizer
    (u : Multiplicative K→*G) (hu : Function.Injective u)
    (f : MulAut G) (hf : u.range.map f.toMonoidHom=u.range)
    (T : Subgroup G)
    (hupper : ∀d∈T,∃c:Kˣ,∀t,d*u (Multiplicative.ofAdd t)*d⁻¹=
      u (Multiplicative.ofAdd ((c:K)*t)))
    (hfull : ∀c:Kˣ,∃d∈T,∀t,d*u (Multiplicative.ofAdd t)*d⁻¹=
      u (Multiplicative.ofAdd ((c:K)*t)))
    (hfT : T.map f.toMonoidHom=T) :
    parameterAut u hu f hf∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) := by
  let A := parameterAut u hu f hf
  have hA (t:K) : u (Multiplicative.ofAdd (A t))=f (u (Multiplicative.ofAdd t)) :=
    parameterAut_apply u hu f hf t
  have hconj (c:Kˣ) : ∃b:Kˣ,
      A*scalarHom K c*A⁻¹=scalarHom K b := by
    obtain ⟨d,hd,hdt⟩ := hfull c
    have hfd : f d∈T := by
      rw [←hfT]
      exact ⟨d,hd,rfl⟩
    obtain ⟨b,hbt⟩ := hupper (f d) hfd
    have hact (t:K) : A ((c:K)*t)=(b:K)*A t := by
      apply Multiplicative.ofAdd.injective
      apply hu
      calc
        u (Multiplicative.ofAdd (A ((c:K)*t)))=f (u (Multiplicative.ofAdd ((c:K)*t))) := hA _
        _=f (d*u (Multiplicative.ofAdd t)*d⁻¹) := congrArg f (hdt t).symm
        _=f d*u (Multiplicative.ofAdd (A t))*(f d)⁻¹ := by
          rw [map_mul,map_mul,map_inv,←hA]
        _=u (Multiplicative.ofAdd ((b:K)*A t)) := hbt (A t)
    refine ⟨b,?_⟩
    ext t
    change A ((c:K)*A.symm t)=(b:K)*t
    rw [hact,A.apply_symm_apply]
  let H := scalarSubgroup K
  let e := MulAut.conj A
  have hle : H.map e.toMonoidHom≤H := by
    rintro _ ⟨_,⟨c,rfl⟩,rfl⟩
    obtain ⟨b,hb⟩ := hconj c
    exact ⟨b,hb.symm⟩
  have hcard : Nat.card (H.map e.toMonoidHom)=Nat.card H :=
    (Nat.card_congr (H.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have heq : H.map e.toMonoidHom=H := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun S:Subgroup (AddAut K)=>(S:Set (AddAut K))) heq

end SymmetricSubgroupAsymptotics.CFSGRootParameterScalarNormalizer
