import SymmetricSubgroupAsymptotics.BinaryBlockKernelAbelian
import SymmetricSubgroupAsymptotics.BlockKernelCentralCoordinate
import SymmetricSubgroupAsymptotics.PrimeIndexAbelianClassCount

/-! Coupled fusion for the actual faithful binary block action with
prime top image. The kernel and its central part are the ORIGINAL
subgroups. The extension may be nonsplit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPrimeTopClassFusion
open OriginalBlockClassBound PrimeIndexAbelianCentralizers
    PrimeIndexAbelianClassCount BinaryBlockKernelAbelian BlockKernelCentralCoordinate

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω)
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2)

include hb hsmall in
theorem prime_top_class_count (p : ℕ) (hp : p.Prime)
    (htop : Nat.card (Top (A:=A) (X:=X))=p) :
    p*Nat.card (ConjClasses A)=Nat.card (Kernel (A:=A) (X:=X))+
      (p^2-1)*Nat.card (centralKernel (Kernel (A:=A) (X:=X))) := by
  letI : IsMulCommutative (Kernel (A:=A) (X:=X)) := kernel_isMulCommutative b hb hsmall
  apply prime_index_abelian_class_count (Kernel (A:=A) (X:=X)) p hp
  exact (Subgroup.index_ker (topMap (A:=A) (X:=X))).trans htop

include hb hsmall in
theorem centralKernel_card_le_two [MulAction.IsPretransitive A X] (x₀:X) :
    Nat.card (centralKernel (Kernel (A:=A) (X:=X)))≤2 := by
  apply (centralKernel_card_le_fibre_permutations b hb x₀).trans
  rw [Nat.card_perm]
  simpa using Nat.factorial_le (hsmall x₀)

include hb hsmall in
theorem prime_top_fusion_bound [Finite X] [MulAction.IsPretransitive A X]
    (x₀:X) (p : ℕ) (hp : p.Prime) (htop : Nat.card (Top (A:=A) (X:=X))=p) :
    p*Nat.card (ConjClasses A)≤2^Nat.card X+(p^2-1)*2 := by
  rw [prime_top_class_count b hb hsmall p hp htop]
  exact Nat.add_le_add (kernel_card_le_power b hb hsmall)
    (Nat.mul_le_mul_left _ (centralKernel_card_le_two b hb hsmall x₀))

end SymmetricSubgroupAsymptotics.BinaryPrimeTopClassFusion
