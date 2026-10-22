import SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootExcludedHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns

/-! An original coordinate reflection preserves the positive roots other
than its own simple root, and the analogous negative statement. Only the
proved sign theorem for norm-two integer vectors is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns CFSGNormTwoGeckSignedRootColumns
open CFSGNormTwoCoordinateExcludedHeight CFSGNormTwoPositiveRootExcludedHeight
open CFSGNormTwoGeckLatticeDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

theorem excludedHeight_reflection (i : Fin r) (k : Roots A) :
    excludedHeight i ((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val=
      excludedHeight i k.val := by
  rw [reflection_val,map_sub,map_smul]
  have hi : excludedHeight i (coordinateRoot A hd i).val=0 := by
    change excludedHeight i (Pi.single i 1)=0
    simp [excludedHeight_single]
  rw [hi,smul_zero,sub_zero]

include ho in
theorem reflection_nonnegative (i : Fin r) (k : Roots A)
    (hpos : ∀j,0≤k.val j) (hne : k≠coordinateRoot A hd i) :
    ∀j,0≤((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val j := by
  have hgt := excludedHeight_positive A hd i k hpos hne
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
      (fun j=>by rw [hd j];exact even_two) ho
      ((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val
      ((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).property with h|h
  · exact h
  · have hbad : excludedHeight i
        ((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val≤0 := by
      rw [excludedHeight_eq_sum_erase]
      exact Finset.sum_nonpos (fun j _=>h j)
    rw [excludedHeight_reflection] at hbad
    omega

theorem reflection_negative_val (i k : Roots A) :
    ((rootPairing A hs hp).reflectionPerm i (negativeIndex A hs hp k)).val=
      -((rootPairing A hs hp).reflectionPerm i k).val := by
  rw [reflection_val,negative_val]
  change reflectionEquiv A i (-k.val)= -reflectionEquiv A i k.val
  exact map_neg _ _

include ho in
theorem reflection_nonpositive (i : Fin r) (k : Roots A)
    (hneg : ∀j,k.val j≤0)
    (hne : negativeIndex A hs hp k≠coordinateRoot A hd i) :
    ∀j,((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val j≤0 := by
  have hpos : ∀j,0≤(negativeIndex A hs hp k).val j := by
    intro j
    rw [negative_val]
    change 0≤ -k.val j
    exact neg_nonneg.mpr (hneg j)
  have href := reflection_nonnegative A hd hs hp ho i (negativeIndex A hs hp k) hpos hne
  intro j
  have hj := href j
  rw [reflection_negative_val] at hj
  change 0≤ -((rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k).val j at hj
  omega

theorem root_signs_incompatible (k : Roots A) (hpos : ∀j,0≤k.val j)
    (hneg : ∀j,k.val j≤0) : False := by
  have hz : k.val=0 := funext (fun j=>le_antisymm (hneg j) (hpos j))
  have hn := k.property
  rw [hz] at hn
  norm_num at hn

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
