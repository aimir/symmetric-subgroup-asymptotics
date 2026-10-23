import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalA2
import SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange

/-! Stabilizing the native positive simple charts forces one field
automorphism on each actual end A2. The sum-root range is recovered from
the actual coefficient-one commutator, not assumed invariant. The middle
edge coupling of these two field maps remains a separate theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalEndFields
open CFSGFFourE6OriginalA2 CFSGFFourE6OriginalSimpleParameters
open CFSGE6GeckFixedOrbitRootGroups CFSGRootParameterAutomorphism
open CFSGCommutatorParameterRange CFSG.Models.Chevalley

private theorem addAut_one_ne_zero {K : Type*} [Field K] (e : K≃+K) : e 1≠0 := by
  intro he
  exact one_ne_zero (e.injective (he.trans (map_zero e).symm))

private theorem edge_parameters_common_field (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K)) (i j : Fin 4)
    (hc : ∀a b : K,originalSimpleHom K false i (Multiplicative.ofAdd a)*
      originalSimpleHom K false j (Multiplicative.ofAdd b)*
      (originalSimpleHom K false i (Multiplicative.ofAdd a))⁻¹*
      (originalSimpleHom K false j (Multiplicative.ofAdd b))⁻¹=
        sumOriginalHom K i j (Multiplicative.ofAdd (a*b)))
    (hfi : (originalSimpleHom K false i).range.map f.toMonoidHom=(originalSimpleHom K false i).range)
    (hfj : (originalSimpleHom K false j).range.map f.toMonoidHom=(originalSimpleHom K false j).range) :
    ∃(tau : RingAut K) (c d : K),c≠0 ∧ d≠0 ∧ ∀a,
      f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
        originalSimpleHom K false i (Multiplicative.ofAdd (c*tau a)) ∧
      f (originalSimpleHom K false j (Multiplicative.ofAdd a))=
        originalSimpleHom K false j (Multiplicative.ofAdd (d*tau a)) := by
  let u := originalSimpleHom K false i
  let v := originalSimpleHom K false j
  let w := sumOriginalHom K i j
  have hu : Function.Injective u := originalSimpleHom_injective K p false i
  have hv : Function.Injective v := originalSimpleHom_injective K p false j
  have hw : Function.Injective w := sumOriginalHom_injective K p i j
  have hfw := commutator_range_map u v w hc f.toMonoidHom hfi hfj
  obtain ⟨tau,htau⟩ := common_field_automorphism_of_commutator u v w hu hv hw hc f hfi hfj hfw
  refine ⟨tau,parameterAut u hu f hfi 1,parameterAut v hv f hfj 1,
    addAut_one_ne_zero _,addAut_one_ne_zero _,?_⟩
  intro a
  exact ⟨(htau a).1,(htau a).2.1⟩

theorem paired_parameters_common_field (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀i,(originalSimpleHom K false i).range.map f.toMonoidHom=(originalSimpleHom K false i).range) :
    ∃(tau : RingAut K) (c d : K),c≠0 ∧ d≠0 ∧ ∀a,
      f (originalSimpleHom K false 0 (Multiplicative.ofAdd a))=
        originalSimpleHom K false 0 (Multiplicative.ofAdd (c*tau a)) ∧
      f (originalSimpleHom K false 1 (Multiplicative.ofAdd a))=
        originalSimpleHom K false 1 (Multiplicative.ofAdd (d*tau a)) :=
  edge_parameters_common_field K p f 0 1
    (original_paired_commutator K 0 1 (by decide)) (hfix 0) (hfix 1)

theorem singleton_parameters_common_field (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀i,(originalSimpleHom K false i).range.map f.toMonoidHom=(originalSimpleHom K false i).range) :
    ∃(tau : RingAut K) (c d : K),c≠0 ∧ d≠0 ∧ ∀a,
      f (originalSimpleHom K false 2 (Multiplicative.ofAdd a))=
        originalSimpleHom K false 2 (Multiplicative.ofAdd (c*tau a)) ∧
      f (originalSimpleHom K false 3 (Multiplicative.ofAdd a))=
        originalSimpleHom K false 3 (Multiplicative.ofAdd (d*tau a)) :=
  edge_parameters_common_field K p f 2 3
    (original_singleton_commutator K 1 0 (by decide)) (hfix 2) (hfix 3)

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalEndFields
