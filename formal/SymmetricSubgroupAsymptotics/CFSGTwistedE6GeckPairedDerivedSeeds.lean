import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedMatrixActions
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DerivedRootImages

/-! Every positive paired simple root has the action of a literal element
of the DERIVED original fixed E6 subgroup. A coefficient-one A2 commutator
and conjugation by an original fixed paired Weyl word work for every q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedDerivedSeeds
open CFSGTwistedE6GeckPairedMatrixActions CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedWeylWords CFSGTwistedE6FixedA2
open CFSGSerreFixedRootElements

theorem paired_positive_action_mem_derived (q : CFSG.PrimePower) (j : Fin 2)
    (t : q.Extension 2) : imageAction q (pairedRoot q false j t)∈(derivedImageAction q).range := by
  let i := j.rev
  have hij : i≠j := by fin_cases j <;> decide
  let c : Derived q := derivedCommutator CartanMatrix.E₆ (q.Extension 2)
    CFSG.Models.e6Twist (fun _=>q.order) (pairedRoot q false i t) (pairedRoot q false j 1)
  let w := pairedWeyl q i
  let d : Derived q := ⟨w⁻¹*c.val*w,by
    simpa only [inv_inv] using
      (inferInstance : (commutator (Fixed q)).Normal).conj_mem c.val c.property w⁻¹⟩
  refine ⟨d,?_⟩
  have he : (matrixPairedWeyl q i)⁻¹*
      ⁅matrixPairedRoot q i t,matrixPairedRoot q j 1⁆*matrixPairedWeyl q i=
        matrixPairedRoot q j t := by
    rw [matrixPaired_commutator q i j hij,one_mul]
    group
  calc
    derivedImageAction q d=imageAction q
        (w⁻¹*⁅pairedRoot q false i t,pairedRoot q false j 1⁆*w) := rfl
    _ = matrixAction (q.Extension 2) ((matrixPairedWeyl q i)⁻¹*
        ⁅matrixPairedRoot q i t,matrixPairedRoot q j 1⁆*matrixPairedWeyl q i) := by
      dsimp only [w]
      simp only [map_mul,map_inv,map_commutatorElement,paired_root_action,paired_weyl_action]
    _ = matrixAction (q.Extension 2) (matrixPairedRoot q j t) := congrArg (matrixAction (q.Extension 2)) he
    _ = imageAction q (pairedRoot q false j t) := (paired_root_action q j t).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedDerivedSeeds
