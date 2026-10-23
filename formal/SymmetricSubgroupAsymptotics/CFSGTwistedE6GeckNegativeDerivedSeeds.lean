import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSingletonDerivedSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedDerivedSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedPairedMatrixActions

/-! Every negative singleton and paired seed has a literal original
Derived action witness. Original fixed Weyl conjugation transports the
proved positive seed witnesses, uniformly in q and characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNegativeDerivedSeeds
open CFSGTwistedE6GeckSingletonDerivedSeeds CFSGTwistedE6GeckPairedDerivedSeeds
open CFSGTwistedE6GeckSignedPairedMatrixActions CFSGTwistedE6GeckPairedMatrixActions
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6FixedA2 CFSGTwistedE6FixedWeylWords CFSGTwistedE6PairedFixedRoots
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoGeckSelfRootConjugation CFSGSerreQuadraticMatrix CFSGSerreOrdinaryTwists

theorem singleton_negative_action_mem_derived (q : CFSG.PrimePower) (j : Fin 2)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t=t) :
    imageAction q (root q true j t ht)∈(derivedImageAction q).range := by
  have hnt : definingFieldAutomorphism q 2 (-t)= -t := by rw [map_neg,ht]
  have hp := singleton_positive_action_mem_derived q j (-t) hnt
  rw [derivedImageAction_eq] at hp
  have hc := CFSGHomDerivedRange.conjugate_mem (imageAction q) (weyl q j) _ hp
  have hmat : matrixSingletonWeyl q j*matrixSingletonRoot q false j (-t)*
      (matrixSingletonWeyl q j)⁻¹=matrixSingletonRoot q true j t := by
    apply Subtype.ext
    change canonicalWeyl rawData (q.Extension 2) (node j)*
      canonicalRoot rawData (q.Extension 2) false (node j) (-t)*
        (canonicalWeyl rawData (q.Extension 2) (node j))⁻¹=
      canonicalRoot rawData (q.Extension 2) true (node j) t
    simpa only [neg_neg] using self_root_word CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index (q.Extension 2) (node j) (-t)
  have he : imageAction q (weyl q j)*imageAction q (root q false j (-t) hnt)*
      (imageAction q (weyl q j))⁻¹=imageAction q (root q true j t ht) := by
    rw [singleton_weyl_action,singleton_root_action,singleton_root_action]
    calc
      _ = matrixAction (q.Extension 2) (matrixSingletonWeyl q j*
          matrixSingletonRoot q false j (-t)*(matrixSingletonWeyl q j)⁻¹) := by
        simp only [map_mul,map_inv]
      _ = _ := congrArg (matrixAction (q.Extension 2)) hmat
  rw [he] at hc
  rw [derivedImageAction_eq]
  exact hc

theorem paired_negative_action_mem_derived (q : CFSG.PrimePower) (j : Fin 2)
    (t : q.Extension 2) : imageAction q (pairedRoot q true j t)∈(derivedImageAction q).range := by
  have hp := paired_positive_action_mem_derived q j (-t)
  rw [derivedImageAction_eq] at hp
  have hc := CFSGHomDerivedRange.conjugate_mem (imageAction q) (pairedWeyl q j) _ hp
  have he : imageAction q (pairedWeyl q j)*imageAction q (pairedRoot q false j (-t))*
      (imageAction q (pairedWeyl q j))⁻¹=imageAction q (pairedRoot q true j t) := by
    rw [paired_weyl_action,paired_root_action,paired_negative_action]
    calc
      _ = matrixAction (q.Extension 2) (matrixPairedWeyl q j*
          matrixPairedRoot q j (-t)*(matrixPairedWeyl q j)⁻¹) := by
        simp only [map_mul,map_inv]
      _ = _ := congrArg (matrixAction (q.Extension 2)) (matrixPaired_self q j t)
  rw [he] at hc
  rw [derivedImageAction_eq]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNegativeDerivedSeeds
