import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive
import Mathlib.Tactic.Group

/-! Kernel-replayable elementary collection steps for constant selected
root parameters in characteristic two. A raised root is kept as the SAME
sumRoot supplied by the proved Chevalley relation. No word normal form,
finite-field action data, or group enumeration is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordCollectionStep
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinateRootPairCommute
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [CommRing K] [CharP K 2]

private theorem sign_cast_one (e : ℤ) (he : e = 1 ∨ e = -1) : (e : K) = 1 := by
  rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]

theorem root_cancel (k : Roots A) :
    selectedRootElement A hd hs hp ho K k 1*selectedRootElement A hd hs hp ho K k 1 = 1 := by
  rw [selectedRootElement_add,CharTwo.add_self_eq_zero,selectedRootElement_zero]

theorem commuting_swap (k l : Roots A)
    (hpair : integerPairing A k.val l.val = 0 ∨ integerPairing A k.val l.val = 1) :
    selectedRootElement A hd hs hp ho K l 1*selectedRootElement A hd hs hp ho K k 1 =
      selectedRootElement A hd hs hp ho K k 1*selectedRootElement A hd hs hp ho K l 1 :=
  (pair_commute A hd hs hp ho K k l hpair 1 1).eq.symm

theorem adjacent_swap (k l : Roots A) (hk : ∀ i,0≤k.val i) (hl : ∀ i,0≤l.val i)
    (hpair : integerPairing A k.val l.val = -1) :
    selectedRootElement A hd hs hp ho K l 1*selectedRootElement A hd hs hp ho K k 1 =
      selectedRootElement A hd hs hp ho K (sumRoot A hs k l hpair) 1*
        selectedRootElement A hd hs hp ho K k 1*selectedRootElement A hd hs hp ho K l 1 := by
  let x := selectedRootElement A hd hs hp ho K k 1
  let y := selectedRootElement A hd hs hp ho K l 1
  let z := selectedRootElement A hd hs hp ho K (sumRoot A hs k l hpair) 1
  obtain ⟨e,he,h⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hpair
  have hc : x*y*x⁻¹*y⁻¹ = z := by
    simpa only [sign_cast_one K e he,one_mul] using h K 1 1
  have hi : z⁻¹ = z := by
    dsimp only [z]
    rw [selectedRootElement_inverse,CharTwo.neg_eq]
  calc
    _ = z⁻¹*x*y := by
      rw [←hc]
      dsimp only [x,y]
      group
    _ = _ := by rw [hi]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordCollectionStep
