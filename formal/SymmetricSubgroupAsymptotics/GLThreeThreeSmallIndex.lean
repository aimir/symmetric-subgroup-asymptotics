import SymmetricSubgroupAsymptotics.StandardGLThreeIndexTwoRecognition
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Fintype.Perm

/-! An actual subgroup of GL3(F3) of index less than thirteen contains
SL3(F3). Its simple determinant kernel cannot act nontrivially on fewer
than thirteen cosets, since its order is divisible by thirteen. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GLThreeThreeSmallIndex
open StandardThreeDimensionalLinearGroups

theorem determinantKernel_le_of_index_lt_thirteen
    (H : Subgroup (GeneralThree 3)) (hi : H.index<13) : determinantKernelThree≤H := by
  letI : IsSimpleGroup determinantKernelThree :=
    simple_determinantKernelThree ProjectiveThreeSimplicity.proved
  let f : determinantKernelThree →* Equiv.Perm (GeneralThree 3 ⧸ H) :=
    (MulAction.toPermHom (GeneralThree 3) (GeneralThree 3 ⧸ H)).comp
      determinantKernelThree.subtype
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb|ht
  · have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hb
    have hd := Subgroup.card_dvd_of_injective f hf
    rw [card_determinantKernelThree,Nat.card_perm,←H.index_eq_card] at hd
    have h13 : 13∣H.index.factorial := (by decide : 13∣5616).trans hd
    have hlo := (show Nat.Prime 13 by decide).dvd_factorial.mp h13
    omega
  · intro x hx
    have hmem : (⟨x,hx⟩ : determinantKernelThree)∈f.ker := by rw [ht]; trivial
    have he : f ⟨x,hx⟩=1 := hmem
    rw [←MulAction.stabilizer_quotient H]
    change x • ((1 : GeneralThree 3) : GeneralThree 3 ⧸ H)=_
    exact DFunLike.congr_fun he ((1 : GeneralThree 3) : GeneralThree 3 ⧸ H)

theorem card_ne_small_index_orders (H : Subgroup (GeneralThree 3)) :
    Nat.card H≠1404 ∧ Nat.card H≠1872 ∧ Nat.card H≠2808 ∧ Nat.card H≠3744 := by
  have hcase (n : ℕ) (hn : n=1404 ∨ n=1872 ∨ n=2808 ∨ n=3744)
      (hH : Nat.card H=n) : False := by
    have hm := H.card_mul_index
    rw [hH,card_GL_three] at hm
    have hi : H.index<13 := by rcases hn with rfl|rfl|rfl|rfl <;> omega
    have hle := determinantKernel_le_of_index_lt_thirteen H hi
    have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [card_determinantKernelThree,hH] at hc
    rcases hn with rfl|rfl|rfl|rfl <;> omega
  exact ⟨hcase 1404 (Or.inl rfl),hcase 1872 (Or.inr (Or.inl rfl)),
    hcase 2808 (Or.inr (Or.inr (Or.inl rfl))),hcase 3744 (Or.inr (Or.inr (Or.inr rfl)))⟩

end SymmetricSubgroupAsymptotics.GLThreeThreeSmallIndex
