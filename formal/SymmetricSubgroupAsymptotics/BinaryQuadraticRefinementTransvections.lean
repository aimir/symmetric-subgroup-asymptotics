import SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-! A binary quadratic refinement has many zero vectors. Transvection
at each zero vector produces a distinct refinement. The count is a
translated nonzero-dot fibre count, and does not classify quadratic
forms or assume transitivity of any isometry group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTransvections

variable {K I : Type} [Field K] [Fintype I]

abbrev Space := (I → K) × (I → K)

def refinement (a b : I → K) (v : Space (K := K) (I := I)) : K :=
  dotProduct v.1 v.2 + dotProduct a v.1 + dotProduct b v.2

def polar (v w : Space (K := K) (I := I)) : K :=
  dotProduct v.1 w.2 + dotProduct w.1 v.2

def transvectionMap (v x : Space (K := K) (I := I)) : Space (K := K) (I := I) :=
  (x.1 + polar v x • v.1, x.2 + polar v x • v.2)

private theorem translated_refinement (a b x y : I → K) :
    refinement a b (x-b,y-a) = dotProduct x y - dotProduct a b := by
  simp only [refinement, sub_dotProduct, dotProduct_sub]
  rw [dotProduct_comm x a, dotProduct_comm b a]
  ring

/-- This lower count holds over every finite field; binary hypotheses
are needed only by the transvection formula below. -/
theorem zero_card_lower [Finite K] (a b : I → K) :
    (Nat.card K ^ Fintype.card I - 1) * Nat.card K ^ (Fintype.card I - 1) ≤
      Nat.card {v : Space (K := K) (I := I) // refinement a b v = 0} := by
  let Q : PUnit → K := fun _ => 0
  let S := HyperbolicNormLevelSliceCardinality.LevelSlice (I := I) Q (dotProduct a b)
  let f : S → {v : Space (K := K) (I := I) // refinement a b v = 0} := fun p =>
    ⟨(p.val.1.1-b,p.val.2-a), by
      rw [translated_refinement]
      have hp : dotProduct p.val.1.1 p.val.2 = dotProduct a b := by
        simpa only [CFSGParabolicQuadricCount.dotDual, Q, add_zero] using p.property.2
      exact sub_eq_zero.mpr hp⟩
  have hf : Function.Injective f := by
    intro p t he
    have hp := congrArg (fun z : {v : Space (K := K) (I := I) // refinement a b v = 0} => z.val) he
    change (p.val.1.1-b,p.val.2-a) = (t.val.1.1-b,t.val.2-a) at hp
    have hx : p.val.1.1 = t.val.1.1 := by
      have hh := congrArg (fun z : Space (K := K) (I := I) => z.1) hp
      simp only [sub_eq_add_neg] at hh
      exact add_right_cancel hh
    have hy : p.val.2 = t.val.2 := by
      have hh := congrArg (fun z : Space (K := K) (I := I) => z.2) hp
      simp only [sub_eq_add_neg] at hh
      exact add_right_cancel hh
    apply Subtype.ext
    exact Prod.ext (Prod.ext hx (Subsingleton.elim _ _)) hy
  have hS : Nat.card S =
      (Nat.card K ^ Fintype.card I - 1) * Nat.card K ^ (Fintype.card I - 1) := by
    simpa only [Nat.card_unique, mul_one] using
      (HyperbolicNormLevelSliceCardinality.card_levelSlice (I := I) Q (dotProduct a b))
  rw [← hS]
  exact Nat.card_le_card_of_injective f hf

private theorem square_eq_self [Finite K] (hK : Nat.card K = 2) (x : K) : x^2=x := by
  letI : Fintype K := Fintype.ofFinite K
  simpa only [← Nat.card_eq_fintype_card, hK] using FiniteField.pow_card x

private theorem shifted_refinement (a b : I → K)
    (v x : Space (K := K) (I := I)) (t : K) :
    refinement a b (x.1+t • v.1,x.2+t • v.2) =
      refinement a b x + t*(dotProduct a v.1+dotProduct b v.2+polar v x) +
        t^2*dotProduct v.1 v.2 := by
  simp only [refinement, polar, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem refinement_transvection [Finite K] (hK : Nat.card K = 2)
    (a b : I → K) (v x : Space (K := K) (I := I)) :
    refinement a b (transvectionMap v x) =
      refinement a b x + (refinement a b v+1)*polar v x := by
  change refinement a b (x.1+polar v x • v.1,x.2+polar v x • v.2) = _
  rw [shifted_refinement]
  have hs := square_eq_self hK (polar v x)
  unfold refinement at *
  linear_combination (dotProduct v.1 v.2+1)*hs

/-- The chart includes v=0. Nondegeneracy is checked on literal standard
coordinate vectors, not supplied as an orbit-separation assumption. -/
theorem transvection_chart_injective [Finite K] (hK : Nat.card K = 2) (a b : I → K) :
    Function.Injective (fun v : {v : Space (K := K) (I := I) // refinement a b v = 0} =>
      fun x : Space (K := K) (I := I) => refinement a b (transvectionMap v.val x)) := by
  classical
  intro v w he
  have hpolar (x : Space (K := K) (I := I)) : polar v.val x = polar w.val x := by
    have hh := congrFun he x
    simp only [refinement_transvection hK, v.property, w.property, zero_add, one_mul] at hh
    exact add_left_cancel hh
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simpa only [polar, dotProduct_zero, zero_dotProduct, dotProduct_single_one,
      add_zero] using hpolar (0,Pi.single i 1)
  · funext i
    simpa only [polar, dotProduct_zero, zero_dotProduct, single_one_dotProduct,
      zero_add] using hpolar (Pi.single i 1,0)

end SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTransvections
