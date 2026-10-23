import SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeComplementRoots
import SymmetricSubgroupAsymptotics.CFSGD4WeylDiscriminant

/-! A selected finite pilot for fixed Weyl-word recognition: when the
central simple root is fixed, pairing and the actual mod-two Weyl
invariants leave exactly two possible outer-root images. Both are
realized by relative short/long words. This is not yet the reduction of
an arbitrary fixed ambient group element to a relative Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWeylPilot
open CFSGIntegerMatrixPairing CFSGTrialityD4PositiveRootOrbits
open CFSGSignedCartanReflections CFSGD4WeylDiscriminant

def cycleCoordinates (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => x (![3,1,0,2] i)

def signedShortCoordinates (neg : Bool) (s k : Fin 3) : Fin 4 → ℤ :=
  if neg then -shortCoordinates s k else shortCoordinates s k

def outerDiscriminants (a : Fin 4 → ℤ) : Prop :=
  (∀ i : Fin 4, ((a i + cycleCoordinates a i : ℤ) : ZMod 2) = discriminantResidue 0 i) ∧
  (∀ i : Fin 4, ((a i + cycleCoordinates (cycleCoordinates a) i : ℤ) : ZMod 2) =
    discriminantResidue 1 i)

theorem central_stabilizer_outer_cases : ∀ (neg : Bool) (s k : Fin 3),
    integerPairing (CartanMatrix.D 4) (signedShortCoordinates neg s k) (longCoordinates 0) = -1 →
    outerDiscriminants (signedShortCoordinates neg s k) →
    (neg = false ∧ s = 0 ∧ k = 0) ∨ (neg = true ∧ s = 1 ∧ k = 0) := by
  unfold outerDiscriminants
  decide

def shortMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1,1,0,0; 0,1,0,0; 0,1,-1,0; 0,1,0,-1]

def longMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,0; 1,-1,1,1; 0,0,1,0; 0,0,0,1]

theorem shortMatrix_eq_word : latticeWord (CartanMatrix.D 4) [0,2,3] = shortMatrix := by decide

theorem longMatrix_eq_step : latticeStep (CartanMatrix.D 4) 1 = longMatrix := by decide

theorem short_long_five_matrix :
    shortMatrix * longMatrix * shortMatrix * longMatrix * shortMatrix = -longMatrix := by decide

private theorem latticeWord_append (u v : List (Fin 4)) :
    latticeWord (CartanMatrix.D 4) (u ++ v) =
      latticeWord (CartanMatrix.D 4) u * latticeWord (CartanMatrix.D 4) v := by
  induction u with
  | nil => simp only [List.nil_append, latticeWord, one_mul]
  | cons i u ih => rw [List.cons_append, latticeWord, ih, latticeWord, mul_assoc]

theorem central_stabilizer_relative_word :
    latticeWord (CartanMatrix.D 4) [0,2,3,1,0,2,3,1,0,2,3] =
      -latticeStep (CartanMatrix.D 4) 1 := by
  have hL : latticeWord (CartanMatrix.D 4) [1] = longMatrix := by
    simp only [latticeWord, mul_one, longMatrix_eq_step]
  change latticeWord (CartanMatrix.D 4)
    ((([0,2,3] ++ [1]) ++ [0,2,3]) ++ [1] ++ [0,2,3]) = _
  simp only [latticeWord_append, shortMatrix_eq_word, hL, longMatrix_eq_step]
  exact short_long_five_matrix

end SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWeylPilot
