import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightBound
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightLayer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-! The finite ORIGINAL positive lattice roots are partitioned by their
actual integer heights. This is not a census of any named exceptional
root system, and assumes no cardinality for its root set. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightPartition
open CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightBound
open CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateRootHeightCommutator
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) [Fintype (Roots A)]

def positiveHeightEquiv :
    (Σn : Fin (rootHeightBound A),ExactHeightRoot A ((n.val:ℤ)+1)) ≃ PositiveRoot A :=
  Equiv.ofBijective (fun p=>p.2.val) (by
    constructor
    · rintro ⟨n,k⟩ ⟨m,l⟩ he
      have hnm : n=m := by
        apply Fin.ext
        have hh := congrArg (fun t : PositiveRoot A=>height t.val.val) he
        dsimp only at hh
        rw [k.property,l.property] at hh
        omega
      cases hnm
      have hkl : k=l := Subtype.ext he
      cases hkl
      rfl
    · intro k
      have hp := positive_root_height_pos A k.val k.property
      have hb := height_le_rootHeightBound A k.val
      have hc : ((height k.val.val).toNat:ℤ)=height k.val.val := Int.toNat_of_nonneg (by omega)
      refine ⟨⟨⟨(height k.val.val).toNat-1,by omega⟩,⟨k,?_⟩⟩,rfl⟩
      change height k.val.val=(((height k.val.val).toNat-1:ℕ):ℤ)+1
      omega)

theorem positive_height_sum_card :
    (∑n∈Finset.range (rootHeightBound A),Nat.card (ExactHeightRoot A ((n:ℤ)+1)))=
      Nat.card (PositiveRoot A) := by
  classical
  have hc := Nat.card_congr (positiveHeightEquiv A)
  rw [Nat.card_sigma] at hc
  calc
    _=∑n : Fin (rootHeightBound A),Nat.card (ExactHeightRoot A ((n.val:ℤ)+1)) :=
      (Fin.sum_univ_eq_sum_range (fun n : ℕ=>Nat.card (ExactHeightRoot A ((n:ℤ)+1))) _).symm
    _=Nat.card (PositiveRoot A) := hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightPartition
