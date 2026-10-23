import SymmetricSubgroupAsymptotics.CFSGTwistedE6PairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGSerreOrthogonalNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification

/-! The four relative simple Weyl words are genuine elements of the
ORIGINAL pinned fixed E6 subgroup. Paired words are regrouped using
original mixed-sign Serre commutation, without natural-image faithfulness
or any assertion that these Weyl words lie in the derived subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWeylWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots
open CFSGSerreOrdinaryTwists

theorem paired_nodes_commute (K : Type) [Field K] (j : Fin 2)
    (e f : Bool) (a b : K) :
    Commute (modelRoot CartanMatrix.E₆ K e (pairedNode j) a)
      (modelRoot CartanMatrix.E₆ K f (CFSG.Models.e6Twist (pairedNode j)) b) :=
  CFSGSerreOrthogonalNodeCommutation.modelRoots_commute_all_signs CartanMatrix.E₆ K
    (pairedNode j) (CFSG.Models.e6Twist (pairedNode j)) (by fin_cases j <;> decide)
    (pairedNode_cartan j) e f a b

theorem neg_one_pow (q : CFSG.PrimePower) : (-1:q.Extension 2)^q.order= -1 := by
  change definingFieldAutomorphism q 2 (-1)= -1
  rw [map_neg,map_one]

def rankOneWord (q : CFSG.PrimePower) (j : Fin 6) : Model CartanMatrix.E₆ (q.Extension 2) :=
  modelRoot CartanMatrix.E₆ (q.Extension 2) false j 1*
    modelRoot CartanMatrix.E₆ (q.Extension 2) true j (-1)*
      modelRoot CartanMatrix.E₆ (q.Extension 2) false j 1

def pairedWeyl (q : CFSG.PrimePower) (j : Fin 2) : Fixed q :=
  pairedRoot q false j 1*pairedRoot q true j (-1)*pairedRoot q false j 1

theorem pairedWeyl_toModel (q : CFSG.PrimePower) (j : Fin 2) :
    toModel q (pairedWeyl q j)=
      rankOneWord q (pairedNode j)*rankOneWord q (CFSG.Models.e6Twist (pairedNode j)) := by
  let a0 := modelRoot CartanMatrix.E₆ (q.Extension 2) false (pairedNode j) 1
  let a1 := modelRoot CartanMatrix.E₆ (q.Extension 2) false (CFSG.Models.e6Twist (pairedNode j)) 1
  let b0 := modelRoot CartanMatrix.E₆ (q.Extension 2) true (pairedNode j) (-1)
  let b1 := modelRoot CartanMatrix.E₆ (q.Extension 2) true (CFSG.Models.e6Twist (pairedNode j)) (-1)
  have hc : Commute a1 b0 := (paired_nodes_commute (q.Extension 2) j true false (-1) 1).symm
  have hd : Commute (a1*b1) a0 :=
    ((paired_nodes_commute (q.Extension 2) j false false 1 1).symm).mul_left
      (paired_nodes_commute (q.Extension 2) j false true 1 (-1)).symm
  dsimp only [pairedWeyl]
  simp only [map_mul,pairedRoot_toModel,one_pow,neg_one_pow]
  change (a0*a1)*(b0*b1)*(a0*a1)=(a0*b0*a0)*(a1*b1*a1)
  rw [hc.mul_mul_mul_comm a0 b1]
  exact hd.mul_mul_mul_comm (a0*b0) a1

def relativeWeyl (q : CFSG.PrimePower) (a : Fin 4) : Fixed q :=
  ![pairedWeyl q 0,pairedWeyl q 1,weyl q 1,weyl q 0] a

def modelWord (q : CFSG.PrimePower) : List (Fin 6)→Model CartanMatrix.E₆ (q.Extension 2)
  | []=>1
  | j::w=>rankOneWord q j*modelWord q w

theorem relativeWeyl_toModel (q : CFSG.PrimePower) (a : Fin 4) :
    toModel q (relativeWeyl q a)=modelWord q (CFSGTwistedE6RelativeWeylOrbits.orbitWord a) := by
  fin_cases a
  · change toModel q (pairedWeyl q 0)=rankOneWord q 0*(rankOneWord q 5*1)
    simpa only [mul_one] using pairedWeyl_toModel q 0
  · change toModel q (pairedWeyl q 1)=rankOneWord q 2*(rankOneWord q 4*1)
    simpa only [mul_one] using pairedWeyl_toModel q 1
  · change toModel q (weyl q 1)=rankOneWord q 3*1
    simpa only [mul_one] using (show toModel q (weyl q 1)=rankOneWord q 3 from rfl)
  · change toModel q (weyl q 0)=rankOneWord q 1*1
    simpa only [mul_one] using (show toModel q (weyl q 0)=rankOneWord q 1 from rfl)

def sourceRelativeWord (q : CFSG.PrimePower) : List (Fin 4)→Fixed q
  | []=>1
  | a::r=>relativeWeyl q a*sourceRelativeWord q r

theorem modelWord_append (q : CFSG.PrimePower) (v w : List (Fin 6)) :
    modelWord q (v++w)=modelWord q v*modelWord q w := by
  induction v with
  | nil=>simp only [List.nil_append,modelWord,one_mul]
  | cons i v ih=>rw [List.cons_append,modelWord,ih,modelWord,mul_assoc]

theorem sourceRelativeWord_toModel (q : CFSG.PrimePower) (r : List (Fin 4)) :
    toModel q (sourceRelativeWord q r)=
      modelWord q (CFSGTwistedE6FixedWordClassification.expandRelative r) := by
  induction r with
  | nil=>rfl
  | cons a r ih=>
    rw [sourceRelativeWord,map_mul,relativeWeyl_toModel,ih,
      CFSGTwistedE6FixedWordClassification.expandRelative,modelWord_append]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWeylWords
