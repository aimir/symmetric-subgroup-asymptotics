import SymmetricSubgroupAsymptotics.PrimeTopPermutationClassFusion
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets

/-! Callback-free binary/ternary fibre consumers for the C2 and C3
top images. All local subgroup budgets are actual degree-at-most-three
permutation bounds. Neither kernel is replaced by a full direct product. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimeTopBlockClassFusion
open OriginalBlockClassBound PrimeTopPermutationClassFusion SmallPermutationClassBudgets
variable {A Ω : Type} [Group A] [MulAction A Ω] [Finite A] [Finite Ω] [FaithfulSMul A Ω]

section Two
variable [MulAction A (Fin 2)] [MulAction.IsPretransitive A (Fin 2)]
    (b:Ω→Fin 2) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_two_top_class_card_le_five
    (htop:Nat.card (Top (A:=A) (X:=Fin 2))=2)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤2) : Nat.card (ConjClasses A)≤5 := by
  have h := prime_top_class_bound b hb 0 2 2 2 Nat.prime_two htop (hsize 0)
    (fun x L=>subgroup_class_card_le_two (hsize x) L)
  simp only [Nat.card_fin] at h
  change 2*Nat.card (ConjClasses A)+2≤12 at h
  omega

include hb in
theorem ternary_two_top_class_card_le_thirteen
    (htop:Nat.card (Top (A:=A) (X:=Fin 2))=2)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤3) : Nat.card (ConjClasses A)≤13 := by
  have h := prime_top_class_bound b hb 0 3 3 2 Nat.prime_two htop (hsize 0)
    (fun x L=>subgroup_class_card_le_three (hsize x) L)
  simp only [Nat.card_fin] at h
  change 2*Nat.card (ConjClasses A)+6≤33 at h
  omega
end Two

section Three
variable [MulAction A (Fin 3)] [MulAction.IsPretransitive A (Fin 3)]
    (b:Ω→Fin 3) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_three_top_class_card_le_eight
    (htop:Nat.card (Top (A:=A) (X:=Fin 3))=3)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤2) : Nat.card (ConjClasses A)≤8 := by
  have h := prime_top_class_bound b hb 0 2 2 3 Nat.prime_three htop (hsize 0)
    (fun x L=>subgroup_class_card_le_two (hsize x) L)
  simp only [Nat.card_fin] at h
  change 3*Nat.card (ConjClasses A)+2≤26 at h
  omega

include hb in
theorem ternary_three_top_class_card_le_twentyFive
    (htop:Nat.card (Top (A:=A) (X:=Fin 3))=3)
    (hsize:∀x,Nat.card (originalBlockFibre b x)≤3) : Nat.card (ConjClasses A)≤25 := by
  have h := prime_top_class_bound b hb 0 3 3 3 Nat.prime_three htop (hsize 0)
    (fun x L=>subgroup_class_card_le_three (hsize x) L)
  simp only [Nat.card_fin] at h
  change 3*Nat.card (ConjClasses A)+6≤81 at h
  omega
end Three

end SymmetricSubgroupAsymptotics.SmallPrimeTopBlockClassFusion
