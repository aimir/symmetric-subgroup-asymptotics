import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DerivedRootImages
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGHomDerivedRange
import Mathlib.Tactic.Group

/-! The fixed E6 singleton nodes 1 and 3 form an actual A2 edge. Every
positive singleton seed acts as a member of the ORIGINAL derived fixed
subgroup, with no restriction on the defining characteristic or q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSingletonDerivedSeeds
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6FixedA2 CFSGTwistedE6FixedWeylWords
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedCollecting CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

def matrixSingletonRoot (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) (t : q.Extension 2) :
    MatrixGroup (q.Extension 2) :=
  canonicalElementaryRoot rawData (q.Extension 2) neg (node j) t

def matrixSingletonWeyl (q : CFSG.PrimePower) (i : Fin 2) : MatrixGroup (q.Extension 2) :=
  matrixRankOneWord (q.Extension 2) (node i)

theorem singleton_root_action (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2)
    (t : q.Extension 2) (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t=t) :
    imageAction q (root q neg j t ht)=matrixAction (q.Extension 2) (matrixSingletonRoot q neg j t) :=
  source_root_action (q.Extension 2) neg (node j) t

theorem singleton_weyl_action (q : CFSG.PrimePower) (i : Fin 2) :
    imageAction q (weyl q i)=matrixAction (q.Extension 2) (matrixSingletonWeyl q i) :=
  rank_one_action q (node i)

theorem derivedImageAction_eq (q : CFSG.PrimePower) :
    derivedImageAction q=CFSGHomDerivedRange.derivedMap (imageAction q) := rfl

theorem matrixSingleton_commutator (q : CFSG.PrimePower) (i j : Fin 2) (hij : i≠j)
    (t : q.Extension 2) :
    ⁅matrixSingletonRoot q false i t,matrixSingletonRoot q false j 1⁆=
      matrixSingletonWeyl q i*matrixSingletonRoot q false j t*(matrixSingletonWeyl q i)⁻¹ := by
  have hcartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index (node i) (node j)= -1 := by
    rw [E6_cartan]
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  apply Subtype.ext
  change canonicalRoot rawData (q.Extension 2) false (node i) t*
    canonicalRoot rawData (q.Extension 2) false (node j) 1*
    (canonicalRoot rawData (q.Extension 2) false (node i) t)⁻¹*
    (canonicalRoot rawData (q.Extension 2) false (node j) 1)⁻¹=
      canonicalWeyl rawData (q.Extension 2) (node i)*
        canonicalRoot rawData (q.Extension 2) false (node j) t*
          (canonicalWeyl rawData (q.Extension 2) (node i))⁻¹
  simpa only [one_mul] using adjacent_word CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index (q.Extension 2) (node i) (node j) hcartan t 1

theorem singleton_positive_action_mem_derived (q : CFSG.PrimePower) (j : Fin 2)
    (t : q.Extension 2) (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t=t) :
    imageAction q (root q false j t ht)∈(derivedImageAction q).range := by
  let i := j.rev
  have hij : i≠j := by fin_cases j <;> decide
  have hm := CFSGHomDerivedRange.commutator_mem (imageAction q)
    (root q false i t ht) (root q false j 1 (one_fixed q))
  have hc := CFSGHomDerivedRange.conjugate_mem (imageAction q) (weyl q i)⁻¹ _ hm
  have hmat : (matrixSingletonWeyl q i)⁻¹*
      ⁅matrixSingletonRoot q false i t,matrixSingletonRoot q false j 1⁆*matrixSingletonWeyl q i=
        matrixSingletonRoot q false j t := by
    rw [matrixSingleton_commutator q i j hij]
    group
  have he : imageAction q ((weyl q i)⁻¹)*
      ⁅imageAction q (root q false i t ht),imageAction q (root q false j 1 (one_fixed q))⁆*
      (imageAction q ((weyl q i)⁻¹))⁻¹=imageAction q (root q false j t ht) := by
    simp only [map_inv,singleton_weyl_action,singleton_root_action]
    calc
      _ = matrixAction (q.Extension 2) ((matrixSingletonWeyl q i)⁻¹*
          ⁅matrixSingletonRoot q false i t,matrixSingletonRoot q false j 1⁆*matrixSingletonWeyl q i) := by
        simp only [map_mul,map_inv,map_commutatorElement,inv_inv]
      _ = _ := congrArg (matrixAction (q.Extension 2)) hmat
  rw [he] at hc
  rw [derivedImageAction_eq]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSingletonDerivedSeeds
