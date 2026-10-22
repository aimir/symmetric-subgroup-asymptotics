import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelectedRootAction

/-! The literal fixed A2 edge of the pinned twisted E6 construction.
Only fixed-subgroup membership is installed here. Its derived subgroup is
retained explicitly, with no assumption that these roots already lie in it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreFixedRootElements
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing
local instance twistedE6FixedA2DecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def node (i : Fin 2) : Fin 6 := ![1,3] i

theorem node_fixed (i : Fin 2) : CFSG.Models.e6Twist (node i)=node i := by
  fin_cases i <;> decide

theorem node_edge : CartanMatrix.E₆ (node 0) (node 1)= -1 := by decide

abbrev Fixed (q : CFSG.PrimePower) :=
  fixedSubgroup CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist (fun _=>q.order)
abbrev Derived (q : CFSG.PrimePower) := commutator (Fixed q)

def root (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) (t : q.Extension 2)
    (ht : definingFieldAutomorphism q 2 t=t) : Fixed q :=
  fixedRoot CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist (fun _=>q.order)
    neg (node i) t (node_fixed i) (by simpa only [definingFieldAutomorphism_apply] using ht)

def toModel (q : CFSG.PrimePower) : Fixed q→*Model CartanMatrix.E₆ (q.Extension 2) :=
  fixedToModel CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist (fun _=>q.order)

def derivedToOriginal (q : CFSG.PrimePower) : Derived q→*Model CartanMatrix.E₆ (q.Extension 2) :=
  derivedToModel CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist (fun _=>q.order)

@[simp] theorem toModel_root (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t=t) :
    toModel q (root q neg i t ht)=modelRoot CartanMatrix.E₆ (q.Extension 2) neg (node i) t := rfl

theorem one_fixed (q : CFSG.PrimePower) : definingFieldAutomorphism q 2 1=1 := map_one _
theorem neg_one_fixed (q : CFSG.PrimePower) : definingFieldAutomorphism q 2 (-1)= -1 := by
  rw [map_neg,map_one]

def weyl (q : CFSG.PrimePower) (i : Fin 2) : Fixed q :=
  root q false i 1 (one_fixed q)*root q true i (-1) (neg_one_fixed q)*
    root q false i 1 (one_fixed q)

def imageAction (q : CFSG.PrimePower) :=
  (imageRepresentation E6Data (q.Extension 2)).comp (toModel q)

theorem root_action (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : definingFieldAutomorphism q 2 t=t)
    (y : (baseChange E6Data (q.Extension 2)).range) :
    (imageAction q (root q neg i t ht) y).val=
      (canonicalRoot E6Data (q.Extension 2) neg (node i) t : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*y.val*
      (↑((canonicalRoot E6Data (q.Extension 2) neg (node i) t)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  change (imageRepresentation E6Data (q.Extension 2)
    (modelRoot CartanMatrix.E₆ (q.Extension 2) neg (node i) t) y).val=_
  exact imageRepresentation_root_selected E6Data (q.Extension 2) neg (node i)
    (E6Data_fourth (q.Extension 2) neg (node i)) t y

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
