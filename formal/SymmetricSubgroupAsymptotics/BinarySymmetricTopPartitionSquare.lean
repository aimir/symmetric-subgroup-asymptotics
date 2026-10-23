import SymmetricSubgroupAsymptotics.BinaryBlockClassGeometricMean
import SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound
import SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport
import Mathlib.Tactic.Ring

/-! The actual full-symmetric-top binary block action, with EVERY
correlated kernel, has a square class bound in terms of ordinary
partitions. No saturation or base class monotonicity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.BinarySymmetricTopPartitionSquare
open OriginalBlockClassBound BinaryBlockWreathCodimension
  PermutationWreathBaseConjugacy

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω),b (a • ω)=a • b ω) (x0 : X)

include hb in
theorem class_square_le_partitions
    (htwo : Nat.card (originalBlockFibre b x0)=2)
    (hTop : Top (A := A) (X := X)=⊤) :
    Nat.card (ConjClasses A)^2≤
      (Nat.card X+1)*4^Nat.card X*Nat.card (Nat.Partition (Nat.card X)) := by
  letI : Fintype X := Fintype.ofFinite _
  letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x0)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr htwo.le
  letI : CommGroup (Equiv.Perm (originalBlockFibre b x0)) := inferInstance
  have hD : Nat.card (Equiv.Perm (originalBlockFibre b x0))=2 := by
    rw [Nat.card_perm,htwo]
    rfl
  let eTop : Top (A := A) (X := X) ≃* Equiv.Perm X :=
    (MulEquiv.subgroupCongr hTop).trans Subgroup.topEquiv
  have hp : Nat.card (ConjClasses (Equiv.Perm X))≤
      Nat.card (Nat.Partition (Nat.card X)) := by
    simpa only [Nat.card_eq_fintype_card (α := X)] using
      (SymmetricConjugacyPartitionBound.class_card_le_partitions (I := X))
  have hT : Nat.card (ConjClasses (Top (A := A) (X := X)))≤
      Nat.card (Nat.Partition (Nat.card X)) :=
    (Nat.card_le_card_of_surjective (ConjClasses.map eTop.symm.toMonoidHom)
      (ConjClasses.map_surjective eTop.symm.surjective)).trans hp
  let eW : FullWreath (A := A) b x0 ≃*
      Wreath (Equiv.Perm (originalBlockFibre b x0)) X :=
    PermutationalWreathProduct.transport eTop (Equiv.refl X) (by intro q i; rfl)
  have hW : Nat.card (ConjClasses (FullWreath (A := A) b x0))≤
      (Nat.card X+1)*2^Nat.card X :=
    (Nat.card_le_card_of_surjective (ConjClasses.map eW.symm.toMonoidHom)
      (ConjClasses.map_surjective eW.symm.surjective)).trans
        (BinaryFullWreathClassBound.class_card_le_coarse (I := X) hD)
  have hmean : Nat.card (ConjClasses A)^2≤2^Nat.card X *
      (Nat.card (ConjClasses (Top (A := A) (X := X))) *
        Nat.card (ConjClasses (FullWreath (A := A) b x0))) := by
    simpa only [Nat.mul_assoc] using
      BinaryBlockClassGeometricMean.class_square_le_actual_top_wreath b hb x0 htwo
  calc
    Nat.card (ConjClasses A)^2≤2^Nat.card X *
        (Nat.card (Nat.Partition (Nat.card X))*((Nat.card X+1)*2^Nat.card X)) :=
      hmean.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul hT hW))
    _=(Nat.card X+1)*4^Nat.card X*Nat.card (Nat.Partition (Nat.card X)) := by
      have hpow : (4:ℕ)^Nat.card X=2^Nat.card X*2^Nat.card X := by
        rw [← mul_pow]
        norm_num
      rw [hpow]
      ring

end SymmetricSubgroupAsymptotics.BinarySymmetricTopPartitionSquare
