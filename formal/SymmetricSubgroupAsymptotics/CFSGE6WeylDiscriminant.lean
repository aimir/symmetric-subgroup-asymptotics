import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport
import Mathlib.Data.ZMod.Basic

/-! A literal mod-three discriminant vector excludes the nontrivial E6
Cartan-diagram permutation from an actual root-lattice Weyl word. This is
an integral obstruction and is independent of the matrix coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6WeylDiscriminant
open CFSGSignedCartanReflections CFSGCartanDiagramLinearAction
open CFSGExceptionalDiagramAutomorphisms CFSGIntegerMatrixColumnTransport

def discriminantLift : Fin 6→ℤ := ![1,0,-1,0,1,-1]
def discriminantResidue : Fin 6→ZMod 3 := ![1,0,-1,0,1,-1]

private theorem residue_eq_cast : discriminantResidue=integerVector (ZMod 3) discriminantLift :=
  by decide

theorem simple_reflection_fixes : ∀i : Fin 6,
    ((Int.castRingHom (ZMod 3)).mapMatrix (latticeStep CartanMatrix.E₆ i))*ᵥ
      discriminantResidue=discriminantResidue := by decide

theorem word_fixes (w : List (Fin 6)) :
    ((Int.castRingHom (ZMod 3)).mapMatrix (latticeWord CartanMatrix.E₆ w))*ᵥ
      discriminantResidue=discriminantResidue := by
  induction w with
  | nil=>simp only [latticeWord,map_one,Matrix.one_mulVec]
  | cons i w ih=>
    simp only [latticeWord,map_mul,←Matrix.mulVec_mulVec]
    rw [ih,simple_reflection_fixes]

theorem diagram_eq_one_of_word_action (w : List (Fin 6)) (σ : Equiv.Perm (Fin 6))
    (hA : ∀i j,CartanMatrix.E₆ (σ i) (σ j)=CartanMatrix.E₆ i j)
    (hword : ∀x : Fin 6→ℤ,latticeWord CartanMatrix.E₆ w*ᵥx=permutationLinear σ x) :
    σ=1 := by
  rcases E6_endpoint σ hA with h0|h0
  · exact E6_fix_zero σ hA h0
  · have h5 : σ 5=0 := by
      have hh := congrArg (fun τ : Equiv.Perm (Fin 6)=>τ 0) (E6_square σ hA)
      change σ (σ 0)=0 at hh
      simpa only [h0] using hh
    have hinv : σ.symm 0=5 := by
      have hh := congrArg σ.symm h5
      simpa only [Equiv.symm_apply_apply] using hh.symm
    have hh := word_fixes w
    rw [residue_eq_cast,map_mulVec,hword discriminantLift] at hh
    have hentry := congrFun hh 0
    change ((discriminantLift (σ.symm 0):ℤ):ZMod 3)=
      ((discriminantLift 0:ℤ):ZMod 3) at hentry
    rw [hinv] at hentry
    exact False.elim ((by decide :
      ((discriminantLift 5:ℤ):ZMod 3)≠((discriminantLift 0:ℤ):ZMod 3)) hentry)

end SymmetricSubgroupAsymptotics.CFSGE6WeylDiscriminant
