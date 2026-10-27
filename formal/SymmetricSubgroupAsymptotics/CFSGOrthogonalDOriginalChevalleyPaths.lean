import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution

/-! Genuine Chevalley transport of the literal signed original D paths.
This does not identify matrix transpose with a Lie homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalChevalleyPaths
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreDividedPowerPaths
open CFSGSerreChevalleyInvolution CFSGOrthogonalDOriginalRootCandidates
variable (r : ℕ) (hr : 4 ≤ r)

theorem map_operator (neg : Bool) (i : Fin r) (k : ℕ) (x : Source r) :
    integralMap (CartanMatrix.D r) (integralOperator (CartanMatrix.D r) neg i k x)=
      integralOperator (CartanMatrix.D r) (!neg) i k (integralMap (CartanMatrix.D r) x) := by
  apply Subtype.ext
  exact rationalMap_dividedPower (CartanMatrix.D r) neg i k x.val

private theorem map_steps (neg : Bool) (ss : List (Fin r×ℕ)) (x : Source r) :
    integralMap (CartanMatrix.D r) (applySteps (CartanMatrix.D r) neg ss x)=
      applySteps (CartanMatrix.D r) (!neg) ss (integralMap (CartanMatrix.D r) x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => simp only [applySteps,ih,map_operator]

private theorem map_pathVector (neg : Bool) (start : Fin r) (ss : List (Fin r×ℕ)) :
    integralMap (CartanMatrix.D r) (pathVector (CartanMatrix.D r) neg start ss)=
      pathVector (CartanMatrix.D r) (!neg) start ss := by
  unfold pathVector
  rw [map_steps]
  congr 1
  apply Subtype.ext
  change rationalMap (CartanMatrix.D r)
    (generator (CartanMatrix.D r) (if neg then .F start else .E start))=
      generator (CartanMatrix.D r) (if !neg then .F start else .E start)
  cases neg
  · exact rationalMap_E (CartanMatrix.D r) start
  · exact rationalMap_F (CartanMatrix.D r) start

theorem map_path_positive (start : Fin r) (ss : List (Fin r)) :
    integralMap (CartanMatrix.D r) (path r false start ss)=
      (-1:ℤ)^ss.length • path r true start ss := by
  simp only [path,Bool.false_eq_true,if_false,if_true,one_smul,map_pathVector]
  rcases neg_one_pow_eq_or ℤ ss.length with h | h <;> simp [h]

theorem map_path_negative (start : Fin r) (ss : List (Fin r)) :
    integralMap (CartanMatrix.D r) (path r true start ss)=
      (-1:ℤ)^ss.length • path r false start ss := by
  simp only [path,Bool.false_eq_true,if_false,if_true,one_smul,map_smul,
    map_pathVector,Bool.not_true]

theorem map_root_swap (neg : Bool) (j : RootIndex r) : ∃ z : ℤ,
    integralMap (CartanMatrix.D r) (root r hr neg j)=z • root r hr (!neg) j := by
  cases neg
  · cases j
    · exact ⟨_,map_path_positive r _ _⟩
    · exact ⟨_,map_path_positive r _ _⟩
  · cases j
    · exact ⟨_,map_path_negative r _ _⟩
    · exact ⟨_,map_path_negative r _ _⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalChevalleyPaths
