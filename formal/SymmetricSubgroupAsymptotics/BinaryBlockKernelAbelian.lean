import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Data.Finite.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A faithful original block kernel on fibres of size at most two is
abelian. Its embedding into the actual fibre permutation groups retains
all correlations; neither full wreath-product structure nor transitivity
is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryBlockKernelAbelian
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite Ω] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω)
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2)

include hb hsmall in
theorem kernel_isMulCommutative : IsMulCommutative (Kernel (A:=A) (X:=X)) where
  is_comm.comm k l := by
    apply coordinates_injective b hb
    funext x
    letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x)) :=
      Equiv.Perm.isMulCommutative_iff_card_le_two.mpr (hsmall x)
    simp only [map_mul]
    exact mul_comm' _ _

include hb hsmall in
theorem kernel_card_le_power [Finite X] :
    Nat.card (Kernel (A:=A) (X:=X))≤2^Nat.card X := by
  letI : Fintype X := Fintype.ofFinite _
  have h := Nat.card_le_card_of_injective
    (fun k x=>coordinate b hb x k) (coordinates_injective b hb)
  rw [Nat.card_pi] at h
  apply h.trans
  calc
    (∏x : X,Nat.card (Equiv.Perm (originalBlockFibre b x)))≤∏_x : X,2 := by
      apply Finset.prod_le_prod'
      intro x _
      rw [Nat.card_perm]
      simpa using Nat.factorial_le (hsmall x)
    _=2^Nat.card X := by
      simp only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.BinaryBlockKernelAbelian
