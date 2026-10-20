import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements
import SymmetricSubgroupAsymptotics.BinaryFourProjectiveSpreadKernelCard
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual projective kernels in rows12/14 have exactly three
members. The upper bound is the checked spread classification; three
original Singer powers give the lower bound. Exact complement orders
then follow through the literal onto projective maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenRows12And14KernelOrders
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14LinearRelations
open BinaryFourProjectiveSpread

private def scalarPowers12 (j : Fin 3) : projective12.ker :=
  ⟨⟨a12^(5*j.val),R12.pow_mem a12_mem _⟩,by
    change projective12 ((⟨a12,a12_mem⟩ : R12)^(5*j.val))=1
    rw [map_pow,projective12_a]
    fin_cases j <;> decide +kernel⟩

private def scalarPowers14 (j : Fin 3) : projective14.ker :=
  ⟨⟨a14^(5*j.val),R14.pow_mem a14_mem _⟩,by
    change projective14 ((⟨a14,a14_mem⟩ : R14)^(5*j.val))=1
    rw [map_pow,projective14_a]
    fin_cases j <;> decide +kernel⟩

private theorem scalarPowers12_injective : Function.Injective scalarPowers12 := by
  have hi : Function.Injective (fun j : Fin 3 =>
      (a12^(5*j.val)) (![1,0,0,0] : Vector)) := by decide +kernel
  intro i j h
  apply hi
  exact congrArg (fun x : projective12.ker => x.val.val (![1,0,0,0] : Vector)) h

private theorem scalarPowers14_injective : Function.Injective scalarPowers14 := by
  have hi : Function.Injective (fun j : Fin 3 =>
      (a14^(5*j.val)) (![1,0,0,0] : Vector)) := by decide +kernel
  intro i j h
  apply hi
  exact congrArg (fun x : projective14.ker => x.val.val (![1,0,0,0] : Vector)) h

theorem kernel12_card : Nat.card projective12.ker=3 := by
  apply Nat.le_antisymm
  · exact action_kernel_card_le_three R12.subtype Subtype.val_injective
      projective12 chart12 projective12_intertwine
  · simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective scalarPowers12 scalarPowers12_injective

theorem kernel14_card : Nat.card projective14.ker=3 := by
  apply Nat.le_antisymm
  · exact action_kernel_card_le_three R14.subtype Subtype.val_injective
      projective14 chart14 projective14_intertwine
  · simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective scalarPowers14 scalarPowers14_injective

theorem evenKernel14_eq : evenProjective14.ker=projective14.ker := by
  ext g
  change evenProjective14 g=1 ↔ projective14 g=1
  constructor
  · exact fun h => congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem evenKernel14_card : Nat.card evenProjective14.ker=3 := by
  rw [evenKernel14_eq,kernel14_card]

theorem card12 : Nat.card R12=360 := by
  have hf := MonoidHom.range_eq_top.mp projective12_range
  have hc : Nat.card (R12 ⧸ projective12.ker)=120 := by
    calc
      _=Nat.card (Equiv.Perm (Fin 5)) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective projective12 hf).toEquiv
      _=120 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup projective12.ker,hc,kernel12_card]

theorem card14 : Nat.card R14=180 := by
  have hc : Nat.card (R14 ⧸ evenProjective14.ker)=60 := by
    calc
      _=Nat.card (alternatingGroup (Fin 5)) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
          evenProjective14 evenProjective14_surjective).toEquiv
      _=60 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 5))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup evenProjective14.ker,hc,evenKernel14_card]

end SymmetricSubgroupAsymptotics.PrimitiveSixteenRows12And14KernelOrders
