import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm

/-! Two literal mod-two discriminant vectors distinguish all D4 diagram
permutations. Every integral Weyl word fixes both vectors; thus a Weyl
word acting by a diagram permutation acts trivially. The obstruction is
independent of the coefficient field of the natural representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGD4WeylDiscriminant
open CFSGSignedCartanReflections CFSGCartanDiagramLinearAction
open CFSGIntegerMatrixColumnTransport

def discriminantLift : Fin 2 → Fin 4 → ℤ :=
  ![![1,0,1,0], ![1,0,0,1]]

def discriminantResidue : Fin 2 → Fin 4 → ZMod 2 :=
  ![![1,0,1,0], ![1,0,0,1]]

private theorem residue_eq_cast : ∀ c : Fin 2,
    discriminantResidue c = integerVector (ZMod 2) (discriminantLift c) := by decide

theorem simple_reflection_fixes : ∀ (i : Fin 4) (c : Fin 2),
    ((Int.castRingHom (ZMod 2)).mapMatrix (latticeStep (CartanMatrix.D 4) i)) *ᵥ
      discriminantResidue c = discriminantResidue c := by decide

theorem word_fixes (w : List (Fin 4)) (c : Fin 2) :
    ((Int.castRingHom (ZMod 2)).mapMatrix (latticeWord (CartanMatrix.D 4) w)) *ᵥ
      discriminantResidue c = discriminantResidue c := by
  induction w with
  | nil => simp only [latticeWord, map_one, Matrix.one_mulVec]
  | cons i w ih =>
    simp only [latticeWord, map_mul, ← Matrix.mulVec_mulVec]
    rw [ih, simple_reflection_fixes]

theorem diagram_eq_one_of_residues : ∀ σ : Equiv.Perm (Fin 4),
    (∀ i j, CartanMatrix.D 4 (σ i) (σ j) = CartanMatrix.D 4 i j) →
    (∀ (c : Fin 2) (i : Fin 4),
      discriminantResidue c (σ.symm i) = discriminantResidue c i) → σ = 1 := by decide

theorem diagram_eq_one_of_word_action (w : List (Fin 4)) (σ : Equiv.Perm (Fin 4))
    (hA : ∀ i j, CartanMatrix.D 4 (σ i) (σ j) = CartanMatrix.D 4 i j)
    (hword : ∀ x : Fin 4 → ℤ,
      latticeWord (CartanMatrix.D 4) w *ᵥ x = permutationLinear σ x) :
    σ = 1 := by
  apply diagram_eq_one_of_residues σ hA
  intro c i
  have hh := word_fixes w c
  rw [residue_eq_cast c, map_mulVec, hword (discriminantLift c)] at hh
  have he := congrFun hh i
  change ((discriminantLift c (σ.symm i) : ℤ) : ZMod 2) =
    ((discriminantLift c i : ℤ) : ZMod 2) at he
  simpa only [residue_eq_cast] using he

end SymmetricSubgroupAsymptotics.CFSGD4WeylDiscriminant
