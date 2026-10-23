import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNegativeDerivedSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections

/-! Every displayed original fixed singleton or paired root section has
its action in the literal original DERIVED fixed-subgroup image. Partner
seed charts are identified using original quadratic Frobenius and actual
orthogonal root commutation; fixed conjugators preserve the derived image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootSections
open CFSGTwistedE6GeckNegativeDerivedSeeds CFSGTwistedE6GeckSingletonDerivedSeeds
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckSourceWordAction
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots CFSGSerreOrdinaryTwists
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix

theorem singletonAt_action_mem_derived (q : CFSG.PrimePower) (j : Fin 6)
    (hj : CFSG.Models.e6Twist j=j) (t : q.Extension 2) (ht : t^q.order=t) :
    imageAction q (singletonAt q j hj t ht)∈(derivedImageAction q).range := by
  have hnodes : ∀j : Fin 6,CFSG.Models.e6Twist j=j → ∃i : Fin 2,node i=j := by decide
  obtain ⟨i,rfl⟩ := hnodes j hj
  have ht' : definingFieldAutomorphism q 2 t=t := ht
  exact singleton_negative_action_mem_derived q i t ht'

theorem pairAt_partner_action (q : CFSG.PrimePower) (i : Fin 2)
    (hj : CFSG.Models.e6Twist (CFSG.Models.e6Twist (pairedNode i))≠
      CFSG.Models.e6Twist (pairedNode i)) (t : q.Extension 2) :
    imageAction q (pairAt q (CFSG.Models.e6Twist (pairedNode i)) hj t)=
      imageAction q (pairedRoot q true i (t^q.order)) := by
  rw [pairAt_action,pairedRoot_action]
  apply congrArg (matrixAction (q.Extension 2))
  apply Subtype.ext
  change canonicalRoot rawData (q.Extension 2) true (CFSG.Models.e6Twist (pairedNode i)) t*
      canonicalRoot rawData (q.Extension 2) true
        (CFSG.Models.e6Twist (CFSG.Models.e6Twist (pairedNode i))) (t^q.order)=
    canonicalRoot rawData (q.Extension 2) true (pairedNode i) (t^q.order)*
      canonicalRoot rawData (q.Extension 2) true (CFSG.Models.e6Twist (pairedNode i))
        ((t^q.order)^q.order)
  rw [node_orbit_two,CFSGTwistedANaturalMatrices.extension_two_pow_twice]
  have hc : CFSGGeckSerreRepresentation.cartan E6Base E6Index (pairedNode i)
      (CFSG.Models.e6Twist (pairedNode i))=0 := by
    rw [E6_cartan]
    exact pairedNode_cartan i
  exact (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index (q.Extension 2) _ _ hc true true (t^q.order) t).symm.eq

theorem pairAt_action_mem_derived (q : CFSG.PrimePower) (j : Fin 6)
    (hj : CFSG.Models.e6Twist j≠j) (t : q.Extension 2) :
    imageAction q (pairAt q j hj t)∈(derivedImageAction q).range := by
  have hnodes : ∀j : Fin 6,CFSG.Models.e6Twist j≠j →
      (∃i : Fin 2,pairedNode i=j) ∨ (∃i : Fin 2,CFSG.Models.e6Twist (pairedNode i)=j) := by decide
  rcases hnodes j hj with ⟨i,rfl⟩|⟨i,rfl⟩
  · exact paired_negative_action_mem_derived q i t
  · rw [pairAt_partner_action]
    exact paired_negative_action_mem_derived q i (t^q.order)

theorem singletonSection_action_mem_derived (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)=sectionNode k)
    (t : q.Extension 2) (ht : t^q.order=t) :
    imageAction q (singletonSection q k hj t ht)∈(derivedImageAction q).range := by
  have hm := singletonAt_action_mem_derived q (sectionNode k) hj t ht
  rw [derivedImageAction_eq] at hm ⊢
  have hc := CFSGHomDerivedRange.conjugate_mem (imageAction q) (sourceTransport q k) _ hm
  simpa only [singletonSection,map_mul,map_inv] using hc

theorem pairedSection_action_mem_derived (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k) (t : q.Extension 2) :
    imageAction q (pairedSection q k hj t)∈(derivedImageAction q).range := by
  have hm := pairAt_action_mem_derived q (sectionNode k) hj t
  rw [derivedImageAction_eq] at hm ⊢
  have hc := CFSGHomDerivedRange.conjugate_mem (imageAction q) (sourceTransport q k) _ hm
  simpa only [pairedSection,map_mul,map_inv] using hc

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootSections
