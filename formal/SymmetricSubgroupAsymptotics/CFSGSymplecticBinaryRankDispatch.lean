import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryModelGeneration

/-! Exact binary type-C rank dispatch with the original excluded C2(2)
guard, retaining the original CFSG model and transferred simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

theorem typeC_binary_twoGenerated_rank (r : ℕ) (q : CFSG.PrimePower)
    (hr : 3≤r) (hq : q.order=2) [IsSimpleGroup (CFSG.Models.C r q)] :
    TwoGenerated (CFSG.Models.C r q) := by
  have he : r=(r-3)+3 := (Nat.sub_add_cancel hr).symm
  letI : IsSimpleGroup (CFSG.Models.C ((r-3)+3) q) := by
    rw [←he]
    infer_instance
  have ht := typeC_binary_twoGenerated (r-3) q hq
  rw [←he] at ht
  exact ht

theorem typeC_binary_twoGenerated_of_index (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2≤r) (hsmall : r=2→q.order≠2) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.C r q)] : TwoGenerated (CFSG.Models.C r q) := by
  have hr3 : 3≤r := by
    have hne : r≠2 := fun he => hsmall he hq
    omega
  exact typeC_binary_twoGenerated_rank r q hr3 hq

end SymmetricSubgroupAsymptotics.CFSGReduction
