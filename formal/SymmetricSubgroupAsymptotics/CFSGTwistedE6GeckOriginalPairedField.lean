import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedA2
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootRigidity

/-! A pair-preserving automorphism of the ORIGINAL twisted E6 group acts
on both positive paired simple-root charts by one field automorphism of
the actual quadratic extension. The third A2 line is recovered from the
proved coefficient-one commutator, rather than assumed invariant. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedField
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckSignedRootRigidity
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalSignedRootAction CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGE6GeckFixedOrbitRootGroups
open CFSGRootParameterAutomorphism CFSGCommutatorParameterRange

private theorem addAut_one_ne_zero {K : Type*} [Field K] (e : K ≃+ K) : e 1 ≠ 0 := by
  intro he
  have h : (1 : K) = 0 := e.injective (he.trans (map_zero e).symm)
  exact one_ne_zero h

theorem paired_ranges_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) (j : Fin 2) :
    (pairedOriginalHom q false j).range.map f.toMonoidHom=(pairedOriginalHom q false j).range := by
  have hh := original_pair_stabilizer_fixes_signed_roots q f hU hV false (pairedOrbit j)
  change (originalOrbitRoot q (pairedOrbit j)).map f.toMonoidHom=originalOrbitRoot q (pairedOrbit j) at hh
  simpa only [originalOrbitRoot_paired] using hh

theorem paired_parameters_common_field (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃ (tau : RingAut (q.Extension 2)) (c d : q.Extension 2), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a,
      f (pairedOriginalHom q false 0 (Multiplicative.ofAdd a))=
        pairedOriginalHom q false 0 (Multiplicative.ofAdd (c*tau a)) ∧
      f (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))=
        pairedOriginalHom q false 1 (Multiplicative.ofAdd (d*tau a)) := by
  let u := pairedOriginalHom q false 0
  let v := pairedOriginalHom q false 1
  let w := pairedSumOriginalHom q 0 1
  have hu : Function.Injective u := pairedOriginalHom_injective q false 0
  have hv : Function.Injective v := pairedOriginalHom_injective q false 1
  have hw : Function.Injective w := pairedSumOriginalHom_injective q 0 1
  have hc : ∀ a b : q.Extension 2,
      u (Multiplicative.ofAdd a)*v (Multiplicative.ofAdd b)*
        (u (Multiplicative.ofAdd a))⁻¹*(v (Multiplicative.ofAdd b))⁻¹=
          w (Multiplicative.ofAdd (a*b)) :=
    original_paired_adjacent_commutator q 0 1 (by decide)
  have hfu : u.range.map f.toMonoidHom=u.range := paired_ranges_fixed q f hU hV 0
  have hfv : v.range.map f.toMonoidHom=v.range := paired_ranges_fixed q f hU hV 1
  have hfw : w.range.map f.toMonoidHom=w.range := commutator_range_map u v w hc f.toMonoidHom hfu hfv
  obtain ⟨tau,htau⟩ := common_field_automorphism_of_commutator u v w hu hv hw hc f hfu hfv hfw
  refine ⟨tau,parameterAut u hu f hfu 1,parameterAut v hv f hfv 1,
    addAut_one_ne_zero _,addAut_one_ne_zero _,?_⟩
  intro a
  exact ⟨(htau a).1,(htau a).2.1⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairedField
