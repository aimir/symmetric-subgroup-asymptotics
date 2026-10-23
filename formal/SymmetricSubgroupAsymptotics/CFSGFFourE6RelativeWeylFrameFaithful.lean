import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedRootFramePilot
import SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber
import Mathlib.Algebra.BigOperators.Pi

/-! Four fixed roots detect actual E6 Weyl-word actions. Their positive
weighted sum is a regular dominant vector. An actual Weyl word fixing
this frame has no negative simple image and is therefore identity.
This does not assert faithfulness for arbitrary commuting linear maps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWeylFrameFaithful
open CFSGFFourE6FixedRootFramePilot CFSGTwistedE6WeylChamber
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylWordDegree CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite

def frameRoot (i:Fin 4) : Roots CartanMatrix.E₆ := ⟨frame i,frame_norm i⟩

theorem regular_pairing (x:Fin 6→ℤ) :
    integerPairing CartanMatrix.E₆ regular x=2*height x := by
  calc
    integerPairing CartanMatrix.E₆ regular x=
        integerPairing CartanMatrix.E₆ regular (∑i:Fin 6,x i • Pi.single i (1:ℤ)) :=
      congrArg (integerPairing CartanMatrix.E₆ regular) (pi_eq_sum_univ' x)
    _=∑i:Fin 6,x i*2 := by
      simp only [map_sum,map_smul,regular_simple_pairing,smul_eq_mul]
    _=2*height x := by
      rw [height,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

theorem pairing_frame_fixed (w:List (Fin 6))
    (hfix:∀i:Fin 4,rootAction w (frameRoot i)=frameRoot i) (k:Roots CartanMatrix.E₆) :
    integerPairing CartanMatrix.E₆ regular (rootAction w k).val=
      integerPairing CartanMatrix.E₆ regular k.val := by
  have hh (i:Fin 4) : integerPairing CartanMatrix.E₆ (frame i) (rootAction w k).val=
      integerPairing CartanMatrix.E₆ (frame i) k.val := by
    have hp := wordRoot_integer_pairing CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index w (frameRoot i) k
    change integerPairing CartanMatrix.E₆ (rootAction w (frameRoot i)).val (rootAction w k).val=
      integerPairing CartanMatrix.E₆ (frame i) k.val at hp
    rw [hfix i] at hp
    exact hp
  rw [regular_combination]
  simp only [map_add,map_nsmul,LinearMap.add_apply,LinearMap.smul_apply]
  rw [hh 0,hh 1,hh 2,hh 3]

theorem linearAction_eq_one_of_frame_fixed (w:List (Fin 6))
    (hfix:∀i:Fin 4,rootAction w (frameRoot i)=frameRoot i) : linearAction w=1 := by
  by_contra hn
  obtain ⟨j,hnegative⟩ := exists_negative_simple w hn
  have hp := pairing_frame_fixed w hfix (E6Index j)
  change integerPairing CartanMatrix.E₆ regular (rootAction w (E6Index j)).val=
    integerPairing CartanMatrix.E₆ regular (Pi.single j (1:ℤ)) at hp
  rw [regular_simple_pairing,regular_pairing] at hp
  have hheight : height (rootAction w (E6Index j)).val≤0 :=
    Finset.sum_nonpos (fun i _=>hnegative i)
  omega

private theorem inverse_root_cancel (v:List (Fin 6)) (k:Roots CartanMatrix.E₆) :
    rootAction (inverseWord v) (rootAction v k)=k := by
  apply Subtype.ext
  rw [←wordLinear_root,←wordLinear_root,wordLinear_inverseWord]
  exact (linearAction v).symm_apply_apply k.val

theorem linearAction_eq_of_frame_eq (w v:List (Fin 6))
    (he:∀i:Fin 4,rootAction w (frameRoot i)=rootAction v (frameRoot i)) :
    linearAction w=linearAction v := by
  have hfix (i:Fin 4) : rootAction (inverseWord v++w) (frameRoot i)=frameRoot i := by
    dsimp only [rootAction] at he ⊢
    rw [wordRoot_append,he i]
    exact inverse_root_cancel v (frameRoot i)
  have hi := linearAction_eq_one_of_frame_fixed (inverseWord v++w) hfix
  change wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
    (inverseWord v++w)=1 at hi
  rw [wordLinear_append,wordLinear_inverseWord] at hi
  exact (inv_mul_eq_one.mp hi).symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWeylFrameFaithful
