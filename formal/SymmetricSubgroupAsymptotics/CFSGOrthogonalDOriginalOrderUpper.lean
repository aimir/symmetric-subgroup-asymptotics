import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import Mathlib.Tactic.Ring

/-! The ORIGINAL type-D model has at most as many elements as its
literal 2r by 2r matrix space. This uses the actual projective
realization and cardinal monotonicity, not an orthogonal order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalOrderUpper
open CFSGOrthogonalDSerreMatrices CFSG.Models.Chevalley

theorem elementaryProjective_card_le_matrix_power (K : Type) [Field K] [Finite K] (r : ℕ) :
    Nat.card (elementaryProjective K r)≤Nat.card K^(4*r^2) := by
  let E := elementaryRootGroup K r
  have hinj : Function.Injective (fun x : E=>(x.val : Mat K r)) := by
    intro x y he
    apply Subtype.ext
    exact Units.ext he
  calc
    Nat.card (elementaryProjective K r)≤Nat.card E :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center E))
        (QuotientGroup.mk'_surjective _)
    _ ≤Nat.card (Mat K r) := Nat.card_le_card_of_injective _ hinj
    _ =Nat.card K^(4*r^2) := by
      change Nat.card (Index r→Index r→K)=_
      simp only [Nat.card_fun,Nat.card_sum,Nat.card_fin,←pow_mul]
      congr 1
      ring

theorem typeD_order_le_matrix_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (CFSG.Models.D r q)≤q.order^(4*r^2) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field s
  rw [Nat.card_congr e.toEquiv]
  simpa only [q.card_field] using elementaryProjective_card_le_matrix_power q.Field (s+4)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalOrderUpper
