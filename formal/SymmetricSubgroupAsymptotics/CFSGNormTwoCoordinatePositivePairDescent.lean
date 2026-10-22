import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGIntegerPairingReflectionDescent

/-! Genuine simultaneous descent of an adjacent positive-root pair.
Reflecting a nonsimple first root in a positively paired simple root
lowers its height and preserves positivity of BOTH roots. The second root
cannot be that simple root because the pair pairing is -1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairDescent
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckSignedRootColumns CFSGNormTwoCoordinateReflectionSigns
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGIntegerPairingPositiveDescent CFSGIntegerPairingReflectionDescent
open CFSGIntegerHeightSign
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem positive_pair_step (k l : Roots A) (hk : ∀j,0≤k.val j) (hl : ∀j,0≤l.val j)
    (hpair : integerPairing A k.val l.val= -1)
    (hnonsimple : ∀i,k≠(s₀ i:Roots A)) :
    ∃i : Fin r,
      (∀j,0≤((rootPairing A hs hp).reflectionPerm (s₀ i) k).val j) ∧
      (∀j,0≤((rootPairing A hs hp).reflectionPerm (s₀ i) l).val j) ∧
      height ((rootPairing A hs hp).reflectionPerm (s₀ i) k).val<height k.val ∧
      integerPairing A ((rootPairing A hs hp).reflectionPerm (s₀ i) k).val
        ((rootPairing A hs hp).reflectionPerm (s₀ i) l).val= -1 := by
  have hnorm : 0 < integerPairing A k.val k.val := by rw [k.property];decide
  obtain ⟨i,_,hi⟩ := exists_positive_coordinate_pairing (integerPairing A) k.val hk hnorm
  have hi' : 0 < integerPairing A k.val (s₀ i:Roots A).val := hi
  have hopp : k.val≠ -(s₀ i:Roots A).val := by
    intro he
    have he' := congrFun he i
    change k.val i= -((Pi.single i (1:ℤ) : Fin r→ℤ) i) at he'
    simp only [Pi.single_apply,if_true] at he'
    have := hk i
    omega
  have hki : integerPairing A k.val (s₀ i:Roots A).val=1 := by
    rcases root_pairing_interior A hs hp k (s₀ i) (hnonsimple i) hopp with h|h|h
    · rw [h] at hi'
      omega
    · rw [h] at hi'
      omega
    · exact h
  have hlne : l≠(s₀ i:Roots A) := by
    intro he
    have hh : integerPairing A k.val (s₀ i:Roots A).val= -1 := by simpa only [he] using hpair
    omega
  refine ⟨i,?_,?_,?_,?_⟩
  · exact reflection_nonnegative A hd hs hp ho i k hk (hnonsimple i)
  · exact reflection_nonnegative A hd hs hp ho i l hl hlne
  · rw [reflection_val,hki]
    change height (k.val-(1:ℤ) • (Pi.single i (1:ℤ) : Fin r→ℤ))<height k.val
    rw [height_coordinate_step]
    omega
  · exact (wordRoot_integer_pairing A hs hp b₀ s₀ [i] k l).trans hpair

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairDescent
