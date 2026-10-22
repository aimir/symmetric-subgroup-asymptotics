import SymmetricSubgroupAsymptotics.CFSGIntegerPairingMixedWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! The elementary integer descent words are exactly actual coordinate
Weyl words, with the order reversal made explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionWords
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGIntegerPairingMixedWord CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckLatticeDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem reflectionWord_eq_wordLinear (w : List (Fin r)) (x : Fin r→ℤ) :
    reflectionWord (integerPairing A) w x=wordLinear A hs hp b₀ s₀ w.reverse x := by
  induction w generalizing x with
  | nil=>rfl
  | cons i w ih=>
    rw [reflectionWord,ih,List.reverse_cons,wordLinear_append]
    rfl

theorem exists_mixed_wordLinear (x : Fin r→ℤ) (hx : ∀i,0≤x i)
    (hnorm : integerPairing A x x=4 ∨ integerPairing A x x=6) :
    ∃(w : List (Fin r)) (a b : Fin r),
      0<wordLinear A hs hp b₀ s₀ w x a ∧ wordLinear A hs hp b₀ s₀ w x b<0 := by
  have haxes : ∀i,integerPairing A (Pi.single i (1:ℤ) : Fin r→ℤ)
      (Pi.single i (1:ℤ) : Fin r→ℤ)=2 := by
    intro i
    change A.toBilin' (Pi.single i (1:ℤ)) (Pi.single i (1:ℤ))=2
    rw [Matrix.toBilin'_single,hd]
  obtain ⟨w,a,b,ha,hb⟩ := exists_mixed_word (integerPairing A)
    (integer_symmetric A hs) haxes x hx hnorm
  refine ⟨w.reverse,a,b,?_,?_⟩
  · rwa [reflectionWord_eq_wordLinear A hd hs hp ho] at ha
  · rwa [reflectionWord_eq_wordLinear A hd hs hp ho] at hb

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionWords
