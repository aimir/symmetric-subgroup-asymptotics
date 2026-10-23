import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMixedA2
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonField
import SymmetricSubgroupAsymptotics.CFSGA2SemilinearRigidity

/-! The SAME field automorphism and reciprocal scalars act on both signs
of the singleton ORIGINAL A2. Negative parameters follow from actual mixed
incidence and intrinsic negative-chart preservation, with no Aut lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonSignedField
open CFSGTwistedE6GeckOriginalMixedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalSingletonField CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckSignedRootRigidity CFSGTwistedE6GeckSignedRootCardinality
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGE6GeckFixedOrbitRootGroups CFSGA2SemilinearRigidity

private theorem parameter_image {K G : Type*} [Field K] [Group G]
    (n : Multiplicative K→*G) (f : G→*G) (hf : n.range.map f=n.range) (a : K) :
    ∃b : K,f (n (Multiplicative.ofAdd a))=n (Multiplicative.ofAdd b) := by
  have hm : f (n (Multiplicative.ofAdd a))∈n.range := by
    rw [←hf]
    exact ⟨_,⟨Multiplicative.ofAdd a,rfl⟩,rfl⟩
  obtain ⟨b,hb⟩ := hm
  exact ⟨b.toAdd,hb.symm⟩

theorem singleton_negative_of_positive (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (i j : Fin 2) (hij : i≠j) (tau : RingAut (Coefficient q)) (c d : Coefficient q)
    (hc : c≠0) (hd : d≠0)
    (hi : ∀a,f (singletonOriginalHom q false i (Multiplicative.ofAdd a))=
      singletonOriginalHom q false i (Multiplicative.ofAdd (c*tau a)))
    (hj : ∀a,f (singletonOriginalHom q false j (Multiplicative.ofAdd a))=
      singletonOriginalHom q false j (Multiplicative.ofAdd (d*tau a))) (a : Coefficient q) :
    f (singletonOriginalHom q true i (Multiplicative.ofAdd a))=
      singletonOriginalHom q true i (Multiplicative.ofAdd (c⁻¹*tau a)) := by
  let u (t : Coefficient q) := singletonOriginalHom q false i (Multiplicative.ofAdd t)
  let v (t : Coefficient q) := singletonOriginalHom q false j (Multiplicative.ofAdd t)
  let n (t : Coefficient q) := singletonOriginalHom q true i (Multiplicative.ofAdd t)
  let w (t : Coefficient q) := singletonSumOriginalHom q i j (Multiplicative.ofAdd t)
  have hp : ∀a b,⁅u a,v b⁆=w (a*b) := original_singleton_adjacent_commutator q i j hij
  have hm : ∀a b,⁅n a,w b⁆=v (a*b) := original_singleton_mixed_commutator q i j hij
  have hw : ∀b,f (w b)=w ((c*d)*tau b) :=
    third_parameter_semilinear u v w hp f.toMonoidHom tau c d hi hj
  have hneg : (singletonOriginalHom q true i).range.map f.toMonoidHom=(singletonOriginalHom q true i).range := by
    simpa only [originalSignedRoot_singleton] using
      original_pair_stabilizer_fixes_signed_roots q f hU hV true (singletonOrbit i)
  exact opposite_parameter_semilinear v n w
    ((singletonOriginalHom_injective q false j).comp Multiplicative.ofAdd.injective)
    hm f.toMonoidHom tau c d hc hd hj hw
    (parameter_image (singletonOriginalHom q true i) f.toMonoidHom hneg) a

theorem singleton_signed_parameters_common_field (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃ (tau : RingAut (Coefficient q)) (c d : Coefficient q), c≠0 ∧ d≠0 ∧ ∀a,
      f (singletonOriginalHom q false 0 (Multiplicative.ofAdd a))=singletonOriginalHom q false 0 (Multiplicative.ofAdd (c*tau a)) ∧
      f (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))=singletonOriginalHom q false 1 (Multiplicative.ofAdd (d*tau a)) ∧
      f (singletonOriginalHom q true 0 (Multiplicative.ofAdd a))=singletonOriginalHom q true 0 (Multiplicative.ofAdd (c⁻¹*tau a)) ∧
      f (singletonOriginalHom q true 1 (Multiplicative.ofAdd a))=singletonOriginalHom q true 1 (Multiplicative.ofAdd (d⁻¹*tau a)) := by
  obtain ⟨tau,c,d,hc,hd,hp⟩ := singleton_parameters_common_field q f hU hV
  refine ⟨tau,c,d,hc,hd,?_⟩
  intro a
  exact ⟨(hp a).1,(hp a).2,
    singleton_negative_of_positive q f hU hV 0 1 (by decide) tau c d hc hd (fun t=>(hp t).1) (fun t=>(hp t).2) a,
    singleton_negative_of_positive q f hU hV 1 0 (by decide) tau d c hd hc (fun t=>(hp t).2) (fun t=>(hp t).1) a⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSingletonSignedField
