import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! A generic matrix-unit subgroup central quotient is no larger than
its full matrix space. The actual original type-C model is then bounded
through its proved elementary projective realization, without a full
symplectic-group identification or group order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MatrixUnitSubgroupOrderUpper

theorem central_quotient_card_le_matrix_space (K I : Type*) [Field K] [Finite K]
    [Fintype I] [DecidableEq I] (U : Subgroup (Matrix I I K)ˣ) :
    Nat.card (U⧸Subgroup.center U) ≤ Nat.card K^(Nat.card I*Nat.card I) := by
  let encode : U → Matrix I I K := fun u => u.val
  have hi : Function.Injective encode := by
    intro u v he
    exact Subtype.ext (Units.ext he)
  calc
    Nat.card (U⧸Subgroup.center U) ≤ Nat.card U :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center U))
        (QuotientGroup.mk'_surjective _)
    _ ≤ Nat.card (Matrix I I K) := Nat.card_le_card_of_injective encode hi
    _ = Nat.card K^(Nat.card I*Nat.card I) := by
      change Nat.card (I → I → K) = _
      rw [Nat.card_fun,Nat.card_fun,←pow_mul]

end SymmetricSubgroupAsymptotics.MatrixUnitSubgroupOrderUpper

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices

theorem typeC_order_le_matrix_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] :
    Nat.card (CFSG.Models.C r q) ≤ q.order^(4*r^2) := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+2 := ⟨r-2,by omega⟩
  let e : CFSG.Models.C (s+2) q ≃* elementaryProjective q.Field (s+2) :=
    serreProjectiveEquivElementaryProjective q.Field (s+1)
  rw [Nat.card_congr e.toEquiv]
  have hc := MatrixUnitSubgroupOrderUpper.central_quotient_card_le_matrix_space
    q.Field (Index (s+2)) (elementaryRootGroup q.Field (s+2))
  have hI : Nat.card (Index (s+2))=2*(s+2) := by
    simp only [Index,Nat.card_sum,Nat.card_fin,two_mul]
  simpa only [hI,q.card_field,
    show 2*(s+2)*(2*(s+2))=4*(s+2)^2 by ring] using hc

end SymmetricSubgroupAsymptotics.CFSGReduction
