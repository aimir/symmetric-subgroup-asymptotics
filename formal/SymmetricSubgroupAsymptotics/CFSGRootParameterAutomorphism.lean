import SymmetricSubgroupAsymptotics.CFSGRootParameterFieldRecognition
import SymmetricSubgroupAsymptotics.CFSGAdditiveAutomorphismTransport
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Actual parameter maps induced by a group automorphism stabilizing
three literal root images. A coefficient-one commutator identity forces
their normalized parameter maps to be the same field automorphism.
Stabilizing the individual images and the commutator identity are explicit
inputs here; they must be proved in each later group application. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
open CFSGAdditiveAutomorphismTransport CFSGRootParameterFieldRecognition
variable {K G : Type*} [Field K] [Group G]

def parameterAut (u : Multiplicative K →* G) (hu : Function.Injective u)
    (f : MulAut G) (hf : u.range.map f.toMonoidHom = u.range) : K ≃+ K :=
  let e := MonoidHom.ofInjective hu
  let r := (f.subgroupMap u.range).trans (MulEquiv.subgroupCongr hf)
  multiplicativeAddAutEquiv K ((e.trans r).trans e.symm)

theorem parameterAut_apply (u : Multiplicative K →* G) (hu : Function.Injective u)
    (f : MulAut G) (hf : u.range.map f.toMonoidHom = u.range) (a : K) :
    u (Multiplicative.ofAdd (parameterAut u hu f hf a)) = f (u (Multiplicative.ofAdd a)) := by
  let e := MonoidHom.ofInjective hu
  let r := (f.subgroupMap u.range).trans (MulEquiv.subgroupCongr hf)
  change u (e.symm (r (e (Multiplicative.ofAdd a)))) = _
  exact congrArg Subtype.val (e.apply_symm_apply (r (e (Multiplicative.ofAdd a))))

theorem parameter_product
    (u v w : Multiplicative K →* G)
    (hu : Function.Injective u) (hv : Function.Injective v) (hw : Function.Injective w)
    (hcomm : ∀ a b : K,
      u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
        (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹ =
          w (Multiplicative.ofAdd (a * b)))
    (f : MulAut G) (hfu : u.range.map f.toMonoidHom = u.range)
    (hfv : v.range.map f.toMonoidHom = v.range)
    (hfw : w.range.map f.toMonoidHom = w.range) (a b : K) :
    parameterAut w hw f hfw (a * b) =
      parameterAut u hu f hfu a * parameterAut v hv f hfv b := by
  apply Multiplicative.ofAdd.injective
  apply hw
  calc
    w (Multiplicative.ofAdd (parameterAut w hw f hfw (a * b))) =
        f (w (Multiplicative.ofAdd (a * b))) := parameterAut_apply w hw f hfw (a * b)
    _ = f (u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
        (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹) := by rw [hcomm]
    _ = f (u (Multiplicative.ofAdd a)) * f (v (Multiplicative.ofAdd b)) *
        (f (u (Multiplicative.ofAdd a)))⁻¹ * (f (v (Multiplicative.ofAdd b)))⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    _ = w (Multiplicative.ofAdd
        (parameterAut u hu f hfu a * parameterAut v hv f hfv b)) := by
      rw [← parameterAut_apply u hu f hfu a, ← parameterAut_apply v hv f hfv b]
      exact hcomm _ _

theorem common_field_automorphism_of_commutator
    (u v w : Multiplicative K →* G)
    (hu : Function.Injective u) (hv : Function.Injective v) (hw : Function.Injective w)
    (hcomm : ∀ a b : K,
      u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
        (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹ =
          w (Multiplicative.ofAdd (a * b)))
    (f : MulAut G) (hfu : u.range.map f.toMonoidHom = u.range)
    (hfv : v.range.map f.toMonoidHom = v.range)
    (hfw : w.range.map f.toMonoidHom = w.range) :
    ∃ σ : K ≃+* K, ∀ a : K,
      f (u (Multiplicative.ofAdd a)) = u (Multiplicative.ofAdd (parameterAut u hu f hfu 1 * σ a)) ∧
      f (v (Multiplicative.ofAdd a)) = v (Multiplicative.ofAdd (parameterAut v hv f hfv 1 * σ a)) ∧
      f (w (Multiplicative.ofAdd a)) = w (Multiplicative.ofAdd (parameterAut w hw f hfw 1 * σ a)) := by
  obtain ⟨σ, hσ, _⟩ := common_field_automorphism
    (parameterAut u hu f hfu) (parameterAut v hv f hfv) (parameterAut w hw f hfw)
    (parameter_product u v w hu hv hw hcomm f hfu hfv hfw)
  refine ⟨σ, ?_⟩
  intro a
  obtain ⟨ha, hb, hc⟩ := hσ a
  constructor
  · rw [← parameterAut_apply u hu f hfu a, ha]
  · constructor
    · rw [← parameterAut_apply v hv f hfv a, hb]
    · rw [← parameterAut_apply w hw f hfw a, hc]

end SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
