import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
import Mathlib.Tactic.Abel

/-! The actual short-node Weyl word is a signed permutation of the eight
literal D4 coordinates. This single sparse identity is integral and does
not require a group census or inversion of a bad prime. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGGTwoShortWeylMatrices
open CFSGGTwoSerreMatrices
open CFSGGTwoShortRootVectorActions

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a, b, c, d] : Fin 4 → R) 2 = c := rfl

private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a, b, c, d] : Fin 4 → R) 3 = d := rfl

def shortWeyl (R : Type*) [CommRing R] : (Mat R)ˣ :=
  rootTransvection R false 0 1 * rootTransvection R true 0 (-1) *
    rootTransvection R false 0 1

def shortSignedMatrix (R : Type*) [CommRing R] : Mat R :=
  -Matrix.single (pos 1) (pos 0) 1 + Matrix.single (pos 0) (pos 1) 1 -
    Matrix.single (neg 1) (neg 0) 1 + Matrix.single (neg 0) (neg 1) 1 -
    Matrix.single (neg 2) (pos 2) 1 - Matrix.single (pos 2) (neg 2) 1 -
    Matrix.single (neg 3) (pos 3) 1 - Matrix.single (pos 3) (neg 3) 1

theorem shortWeyl_apply (R : Type*) [CommRing R] (v : Index → R) :
    (shortWeyl R : Mat R) *ᵥ v = shortSignedMatrix R *ᵥ v := by
  simp only [shortWeyl, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [positive_apply, negative_apply, positive_apply]
  simp only [shortSignedMatrix, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.neg_mulVec, Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    norm_num [positiveAction, negativeAction, pos, neg, Function.update_apply,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff, vec4_two, vec4_three] <;> ring

theorem shortWeyl_val (R : Type*) [CommRing R] :
    (shortWeyl R : Mat R) = shortSignedMatrix R := by
  apply Matrix.ext_of_mulVec_single
  intro j
  exact shortWeyl_apply R (Pi.single j 1)

def naturalShortWeyl (K : Type) [Field K] : naturalGroup K :=
  naturalRoot K false 0 1 * naturalRoot K true 0 (-1) * naturalRoot K false 0 1

theorem naturalShortWeyl_val (K : Type) [Field K] :
    (naturalShortWeyl K).val = shortWeyl K := rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoShortWeylMatrices
