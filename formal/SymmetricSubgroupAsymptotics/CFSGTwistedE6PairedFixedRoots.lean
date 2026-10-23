import SymmetricSubgroupAsymptotics.CFSGSerrePairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The two actual orthogonal E6 node pairs supply root words in the
ORIGINAL pinned fixed subgroup for every quadratic-extension parameter.
The proof uses original integral Serre commutation; no natural-matrix
faithfulness or derived membership is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6PairedFixedRoots
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGTwistedE6FixedA2

def pairedNode (j : Fin 2) : Fin 6 := ![0,2] j

theorem pairedNode_cartan (j : Fin 2) :
    CartanMatrix.E₆ (pairedNode j) (CFSG.Models.e6Twist (pairedNode j))=0 := by
  fin_cases j <;> decide

theorem pairedNode_orbit_two (j : Fin 2) :
    CFSG.Models.e6Twist (CFSG.Models.e6Twist (pairedNode j))=pairedNode j := by
  fin_cases j <;> decide

def pairedRoot (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) (t : q.Extension 2) : Fixed q :=
  CFSGSerrePairedFixedRoots.pairedFixedRoot CartanMatrix.E₆ (q.Extension 2)
    CFSG.Models.e6Twist (fun _=>q.order) neg (pairedNode j) (pairedNode_cartan j)
    (pairedNode_orbit_two j) t
    (CFSGTwistedANaturalMatrices.extension_two_pow_twice q t)

theorem pairedRoot_toModel (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) (t : q.Extension 2) :
    toModel q (pairedRoot q neg j t)=
      modelRoot CartanMatrix.E₆ (q.Extension 2) neg (pairedNode j) t*
        modelRoot CartanMatrix.E₆ (q.Extension 2) neg
          (CFSG.Models.e6Twist (pairedNode j)) (t^q.order) := rfl

theorem pairedRoot_zero_toModel (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    toModel q (pairedRoot q neg 0 t)=
      modelRoot CartanMatrix.E₆ (q.Extension 2) neg 0 t*
        modelRoot CartanMatrix.E₆ (q.Extension 2) neg 5 (t^q.order) := rfl

theorem pairedRoot_one_toModel (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    toModel q (pairedRoot q neg 1 t)=
      modelRoot CartanMatrix.E₆ (q.Extension 2) neg 2 t*
        modelRoot CartanMatrix.E₆ (q.Extension 2) neg 4 (t^q.order) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6PairedFixedRoots
