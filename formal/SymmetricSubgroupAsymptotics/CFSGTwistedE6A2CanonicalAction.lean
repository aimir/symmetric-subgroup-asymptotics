import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2

/-! Fixed A2 root words intertwine with their literal canonical E6 matrix
words on the SAME original E6 tensor image. This equality is a consequence
of the checked E6 image constraint, not a group recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing
local instance twistedE6A2CanonicalActionDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev Canonical (q : CFSG.PrimePower) := canonicalElementaryGroup E6Data (q.Extension 2)

def naturalRoot (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) (t : q.Extension 2) : Canonical q :=
  canonicalElementaryRoot E6Data (q.Extension 2) neg (node i) t

def naturalWeyl (q : CFSG.PrimePower) (i : Fin 2) : Canonical q :=
  naturalRoot q false i 1*naturalRoot q true i (-1)*naturalRoot q false i 1

def canonicalAction (q : CFSG.PrimePower) :=
  canonicalImageAction E6Data (q.Extension 2) (E6Data_fourth (q.Extension 2))

theorem imageAction_root_eq_canonical (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t=t) :
    imageAction q (root q neg i t ht)=canonicalAction q (naturalRoot q neg i t) := by
  change imageRepresentation E6Data (q.Extension 2)
      (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.E₆ (q.Extension 2) neg (node i) t)=_
  exact source_root_action_eq_elementary E6Data (q.Extension 2)
    (canonicalRoot E6Data (q.Extension 2)) (canonicalRoot_val E6Data (q.Extension 2))
    (canonicalRoot_inv_val E6Data (q.Extension 2)) (E6Data_fourth (q.Extension 2)) neg (node i) t

theorem imageAction_weyl_eq_canonical (q : CFSG.PrimePower) (i : Fin 2) :
    imageAction q (weyl q i)=canonicalAction q (naturalWeyl q i) := by
  simp only [weyl,naturalWeyl,map_mul,imageAction_root_eq_canonical]

@[simp] theorem naturalRoot_val (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) (t : q.Extension 2) :
    (naturalRoot q neg i t).val=canonicalRoot E6Data (q.Extension 2) neg (node i) t := rfl
@[simp] theorem naturalWeyl_val (q : CFSG.PrimePower) (i : Fin 2) :
    (naturalWeyl q i).val=canonicalWeyl E6Data (q.Extension 2) (node i) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
