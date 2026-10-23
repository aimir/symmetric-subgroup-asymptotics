import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import SymmetricSubgroupAsymptotics.PrimeIndexAbelianCentralizers

/-! The ORIGINAL central part of a block kernel is detected by one
literal fibre coordinate. Transitivity is needed only on the block set.
The proof uses actual conjugate evaluations; it does not assert that
class numbers are monotone under subgroup inclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BlockKernelCentralCoordinate
open OriginalBlockClassBound PrimeIndexAbelianCentralizers

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω) (x₀:X)

def centralCoordinate : centralKernel (Kernel (A:=A) (X:=X))→*
    Equiv.Perm (originalBlockFibre b x₀) :=
  (coordinate b hb x₀).comp (centralKernel (Kernel (A:=A) (X:=X))).subtype

include hb in
theorem centralCoordinate_injective [FaithfulSMul A Ω] [MulAction.IsPretransitive A X] :
    Function.Injective (centralCoordinate b hb x₀) := by
  apply (centralCoordinate b hb x₀).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro c hc
  have he : originalBlockEvaluation b hb x₀ (Kernel (A:=A) (X:=X)) le_rfl c.val=1 := by
    apply Subtype.ext
    exact hc
  have hn : c.val=1 := originalBlockEvaluation_conjugates_separate b hb x₀
      (Kernel (A:=A) (X:=X)) le_rfl c.val (fun a=>by
    have hfix : MulAut.conjNormal a c.val=c.val := by
      apply Subtype.ext
      change a*(c.val:A)*a⁻¹=(c.val:A)
      have hcomm : a*(c.val:A)=(c.val:A)*a := Subgroup.mem_center_iff.mp c.property a
      rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
    rw [hfix]
    exact he)
  exact Subgroup.mem_bot.mpr (Subtype.ext hn)

include hb in
theorem centralKernel_card_le_fibre_permutations [Finite Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A X] :
    Nat.card (centralKernel (Kernel (A:=A) (X:=X)))≤
      Nat.card (Equiv.Perm (originalBlockFibre b x₀)) :=
  Nat.card_le_card_of_injective (centralCoordinate b hb x₀)
    (centralCoordinate_injective b hb x₀)

end SymmetricSubgroupAsymptotics.BlockKernelCentralCoordinate
