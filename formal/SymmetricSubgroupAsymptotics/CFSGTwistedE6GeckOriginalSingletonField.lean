import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonA2
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootRigidity

/-! A pair-preserving automorphism of the ORIGINAL twisted E6 group acts
on both positive singleton simple-root charts by one field automorphism of
the actual fixed coefficient subfield. The third A2 line is recovered from the
proved coefficient-one commutator, rather than assumed invariant. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonField
open CFSGTwistedE6GeckOriginalSingletonA2 CFSGTwistedE6GeckSignedRootRigidity
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalSignedRootAction CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGE6GeckFixedOrbitRootGroups
open CFSGRootParameterAutomorphism CFSGCommutatorParameterRange

private theorem addAut_one_ne_zero {K : Type*} [Field K] (e : K ≃+ K) : e 1 ≠ 0 := by
  intro he
  have h : (1 : K) = 0 := e.injective (he.trans (map_zero e).symm)
  exact one_ne_zero h

theorem singleton_ranges_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) (j : Fin 2) :
    (singletonOriginalHom q false j).range.map f.toMonoidHom=(singletonOriginalHom q false j).range := by
  have hh := original_pair_stabilizer_fixes_signed_roots q f hU hV false (singletonOrbit j)
  change (originalOrbitRoot q (singletonOrbit j)).map f.toMonoidHom=originalOrbitRoot q (singletonOrbit j) at hh
  simpa only [originalOrbitRoot_singleton] using hh

theorem singleton_parameters_common_field (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃ (tau : RingAut (Coefficient q)) (c d : Coefficient q), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a,
      f (singletonOriginalHom q false 0 (Multiplicative.ofAdd a))=
        singletonOriginalHom q false 0 (Multiplicative.ofAdd (c*tau a)) ∧
      f (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))=
        singletonOriginalHom q false 1 (Multiplicative.ofAdd (d*tau a)) := by
  let u := singletonOriginalHom q false 0
  let v := singletonOriginalHom q false 1
  let w := singletonSumOriginalHom q 0 1
  have hu : Function.Injective u := singletonOriginalHom_injective q false 0
  have hv : Function.Injective v := singletonOriginalHom_injective q false 1
  have hw : Function.Injective w := singletonSumOriginalHom_injective q 0 1
  have hc : ∀ a b : Coefficient q,
      u (Multiplicative.ofAdd a)*v (Multiplicative.ofAdd b)*
        (u (Multiplicative.ofAdd a))⁻¹*(v (Multiplicative.ofAdd b))⁻¹=
          w (Multiplicative.ofAdd (a*b)) :=
    original_singleton_adjacent_commutator q 0 1 (by decide)
  have hfu : u.range.map f.toMonoidHom=u.range := singleton_ranges_fixed q f hU hV 0
  have hfv : v.range.map f.toMonoidHom=v.range := singleton_ranges_fixed q f hU hV 1
  have hfw : w.range.map f.toMonoidHom=w.range := commutator_range_map u v w hc f.toMonoidHom hfu hfv
  obtain ⟨tau,htau⟩ := common_field_automorphism_of_commutator u v w hu hv hw hc f hfu hfv hfw
  refine ⟨tau,parameterAut u hu f hfu 1,parameterAut v hv f hfv 1,
    addAut_one_ne_zero _,addAut_one_ne_zero _,?_⟩
  intro a
  exact ⟨(htau a).1,(htau a).2.1⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonField
