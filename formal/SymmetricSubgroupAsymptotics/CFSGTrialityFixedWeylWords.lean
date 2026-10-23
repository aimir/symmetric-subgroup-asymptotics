import SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
import SymmetricSubgroupAsymptotics.CFSGSerreOrthogonalNodeCommutation

/-! Two literal Weyl words in the ORIGINAL triality fixed subgroup.
The short word maps to the product at nodes 0,2,3 by original mixed-sign
root commutation. No matrix faithfulness or derived membership is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityFixedWeylWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreFixedRootElements
open CFSGSerreOrdinaryTwists CFSGTrialityTripleFixedRoots

private theorem triple_product {G : Type*} [Monoid G] (a b : Fin 3 → G)
    (h10 : Commute (a 1) (b 0)) (h20 : Commute (a 2) (b 0))
    (h21 : Commute (a 2) (b 1)) :
    (a 0 * a 1 * a 2) * (b 0 * b 1 * b 2) =
      (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) := by
  calc
    _ = (a 0 * a 1) * (b 0 * b 1) * (a 2 * b 2) :=
      (h20.mul_right h21).mul_mul_mul_comm _ _
    _ = _ := congrArg (fun x => x * (a 2 * b 2))
      (h10.mul_mul_mul_comm (a 0) (b 1))

def outerNode : Fin 3 → Fin 4 := ![0,2,3]

theorem outerNode_injective : Function.Injective outerNode := by decide

theorem outerNode_cartan (i j : Fin 3) (hij : i ≠ j) :
    CartanMatrix.D 4 (outerNode i) (outerNode j) = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outerNode, CartanMatrix.D] at * <;> decide

theorem outer_roots_commute (K : Type) [Field K] (i j : Fin 3) (hij : i ≠ j)
    (e f : Bool) (a b : K) :
    Commute (modelRoot (CartanMatrix.D 4) K e (outerNode i) a)
      (modelRoot (CartanMatrix.D 4) K f (outerNode j) b) :=
  CFSGSerreOrthogonalNodeCommutation.modelRoots_commute_all_signs
    (CartanMatrix.D 4) K (outerNode i) (outerNode j)
    (fun h => hij (outerNode_injective h)) (outerNode_cartan i j hij) e f a b

theorem neg_one_pow (q : CFSG.PrimePower) :
    (-1 : q.Extension 3)^q.order = -1 := by
  change definingFieldAutomorphism q 3 (-1) = -1
  simp only [map_neg, map_one]

def rankOneWord (q : CFSG.PrimePower) (j : Fin 4) :
    Model (CartanMatrix.D 4) (q.Extension 3) :=
  modelRoot (CartanMatrix.D 4) (q.Extension 3) false j 1 *
    modelRoot (CartanMatrix.D 4) (q.Extension 3) true j (-1) *
    modelRoot (CartanMatrix.D 4) (q.Extension 3) false j 1

def shortWeyl (q : CFSG.PrimePower) : Fixed q :=
  orbitRoot q false 1 * orbitRoot q true (-1) * orbitRoot q false 1

def longRoot (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3)
    (ht : t^q.order = t) : Fixed q :=
  fixedRoot (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
    (fun _ => q.order) neg 1 t (by decide) ht

theorem longRoot_toModel (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3)
    (ht : t^q.order = t) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (longRoot q neg t ht) =
        modelRoot (CartanMatrix.D 4) (q.Extension 3) neg 1 t := rfl

def longWeyl (q : CFSG.PrimePower) : Fixed q :=
  longRoot q false 1 (one_pow _) * longRoot q true (-1) (neg_one_pow q) *
    longRoot q false 1 (one_pow _)

theorem shortWeyl_toModel (q : CFSG.PrimePower) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (shortWeyl q) =
        rankOneWord q 0 * rankOneWord q 2 * rankOneWord q 3 := by
  let a := fun j : Fin 3 => modelRoot (CartanMatrix.D 4) (q.Extension 3)
    false (outerNode j) 1
  let b := fun j : Fin 3 => modelRoot (CartanMatrix.D 4) (q.Extension 3)
    true (outerNode j) (-1)
  change _ = (a 0 * b 0 * a 0) * (a 1 * b 1 * a 1) * (a 2 * b 2 * a 2)
  dsimp only [shortWeyl]
  simp only [map_mul, orbitRoot_toModel, one_pow, neg_one_pow]
  change (a 0 * a 1 * a 2) * (b 0 * b 1 * b 2) * (a 0 * a 1 * a 2) = _
  have hc : ∀ i j : Fin 3, i ≠ j → Commute (a i) (b j) := by
    intro i j hij
    exact outer_roots_commute (q.Extension 3) i j hij false true 1 (-1)
  have hd : ∀ i j : Fin 3, i ≠ j → Commute (a i * b i) (a j) := by
    intro i j hij
    exact (outer_roots_commute (q.Extension 3) i j hij false false 1 1).mul_left
      (outer_roots_commute (q.Extension 3) i j hij true false (-1) 1)
  rw [triple_product a b (hc 1 0 (by decide)) (hc 2 0 (by decide))
    (hc 2 1 (by decide))]
  exact triple_product (fun j => a j * b j) a
    (hd 1 0 (by decide)) (hd 2 0 (by decide)) (hd 2 1 (by decide))

theorem longWeyl_toModel (q : CFSG.PrimePower) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (longWeyl q) = rankOneWord q 1 := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityFixedWeylWords
