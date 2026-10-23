import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator

/-! Typed SAME-group matrix actions for the original paired fixed roots
and Weyl words, including the coefficient-one paired A2 commutator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedMatrixActions
open CFSGTwistedE6GeckPairedA2Commutator CFSGTwistedE6GeckSourceWordAction
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedWeylWords CFSGTwistedE6FixedA2
open CFSGSerreQuadraticMatrix CFSGSerreOrdinaryTwists CFSG.Models.Chevalley

def matrixPairedRoot (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    MatrixGroup (q.Extension 2) :=
  canonicalElementaryRoot rawData (q.Extension 2) false (pairedNode j) t*
    canonicalElementaryRoot rawData (q.Extension 2) false
      (CFSG.Models.e6Twist (pairedNode j)) (t^q.order)

def matrixPairedWeyl (q : CFSG.PrimePower) (i : Fin 2) : MatrixGroup (q.Extension 2) :=
  matrixRankOneWord (q.Extension 2) (pairedNode i)*
    matrixRankOneWord (q.Extension 2) (CFSG.Models.e6Twist (pairedNode i))

theorem matrixPairedRoot_val (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    (matrixPairedRoot q j t).val=
      pairedMatrixRoot (q.Extension 2) (definingFieldAutomorphism q 2) j t := by
  change canonicalRoot rawData (q.Extension 2) false (pairedNode j) t*
    canonicalRoot rawData (q.Extension 2) false (CFSG.Models.e6Twist (pairedNode j)) (t^q.order)=
      canonicalRoot rawData (q.Extension 2) false (pairedNode j) t*
        canonicalRoot rawData (q.Extension 2) false (CFSG.Models.e6Twist (pairedNode j))
          (definingFieldAutomorphism q 2 t)
  rw [definingFieldAutomorphism_apply]

theorem matrixPairedWeyl_val (q : CFSG.PrimePower) (i : Fin 2) :
    (matrixPairedWeyl q i).val=pairedMatrixWeyl (q.Extension 2) i := rfl

theorem paired_root_action (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    imageAction q (pairedRoot q false j t)=matrixAction (q.Extension 2) (matrixPairedRoot q j t) :=
  pairedRoot_action q false j t

theorem paired_weyl_action (q : CFSG.PrimePower) (i : Fin 2) :
    imageAction q (pairedWeyl q i)=matrixAction (q.Extension 2) (matrixPairedWeyl q i) := by
  change imageRepresentation data (q.Extension 2) (toModel q (pairedWeyl q i))=_
  rw [pairedWeyl_toModel,map_mul,rank_one_action,rank_one_action]
  exact (map_mul (matrixAction (q.Extension 2)) _ _).symm

theorem matrixPaired_commutator (q : CFSG.PrimePower) (i j : Fin 2) (hij : i≠j)
    (t a : q.Extension 2) :
    ⁅matrixPairedRoot q i t,matrixPairedRoot q j a⁆=
      matrixPairedWeyl q i*matrixPairedRoot q j (a*t)*(matrixPairedWeyl q i)⁻¹ := by
  apply Subtype.ext
  simp only [commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv,
    matrixPairedRoot_val,matrixPairedWeyl_val]
  exact paired_adjacent_commutator (q.Extension 2) (definingFieldAutomorphism q 2) i j hij t a

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedMatrixActions
