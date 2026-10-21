import SymmetricSubgroupAsymptotics.BinaryPairIntegralMixedBudget
import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter

/-! Actual mixed commutator cuts can also be detected by a small faithful
top-kernel capacity, including the exact half-dimensional boundary. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- Every top element of the SAME normal subgroup satisfies its actual
mixed-displacement constraint. -/
theorem normal_top_card_le_displacement_capacity
    (E L : Subgroup U) [E.Normal]
    (hcut : ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker ≤ L) :
    Nat.card (E.map F.top.rangeRestrict) ≤
      Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
        F.coordinateTopAction t v - v ∈ F.ambientAxis L} := by
  have hm (e : U) (he : e ∈ E) (k : F.top.ker) :
      F.coordinateTopAction (F.top.rangeRestrict e) (F.bits k) - F.bits k ∈
        F.ambientAxis L := by
    let d : F.top.ker := k⁻¹ * MulAut.conjNormal e k
    have hc : (d : U) ∈ ⁅E, (⊤ : Subgroup U)⁆ := by
      have hc0 := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((k : U)⁻¹)) he
      rw [Subgroup.commutator_comm] at hc0
      change (k : U)⁻¹ * e * (k : U) * e⁻¹ ∈ ⁅E, (⊤ : Subgroup U)⁆ at hc0
      change (k : U)⁻¹ * (e * (k : U) * e⁻¹) ∈ ⁅E, (⊤ : Subgroup U)⁆
      simpa only [mul_assoc] using hc0
    have hv := (F.bits_mem_ambientAxis L d).mpr (hcut ⟨hc, d.property⟩)
    change F.bits (k⁻¹ * MulAut.conjNormal e k) ∈ F.ambientAxis L at hv
    rwa [F.bits_commutator] at hv
  let j : E.map F.top.rangeRestrict →
      {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
        F.coordinateTopAction t v - v ∈ F.ambientAxis L} := fun t => ⟨t.val, by
    obtain ⟨e, he, ht⟩ := t.property
    rw [← ht]
    intro v hv
    obtain ⟨k, hk⟩ := hv
    change F.bits k.toMul = v at hk
    rw [← hk]
    exact hm e he k.toMul⟩
  exact Nat.card_le_card_of_injective j (by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
      F.coordinateTopAction t v - v ∈ F.ambientAxis L} => z.val) h)

/-- A genuine mixed bit halves a relative head-two intersection price.
Every factor in this inequality refers to the original E and its image. -/
theorem integral_order_le_two_mul_top_of_displacement_gap
    (E L : Subgroup U) [E.Normal]
    (hL : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker)
    (hgap : Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
      F.coordinateTopAction t v - v ∈ F.ambientAxis L} <
        Nat.card (E.map F.top.rangeRestrict))
    (hA : Nat.card (E ⊓ F.top.ker : Subgroup U) ≤ 4 * Nat.card L) :
    normalIntegralCoinvariantOrder E ≤
      2 * normalIntegralCoinvariantOrder (E.map F.top.rangeRestrict) := by
  have hnot : ¬ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker ≤ L := by
    intro hc
    exact (not_lt_of_ge (F.normal_top_card_le_displacement_capacity E L hc)) hgap
  have hc := two_mul_inf_card_le_of_not_le L
    (⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker) hnot
  rw [inf_eq_left.mpr hL] at hc
  apply normalIntegralCoinvariantOrder_le_of_actual_intersection_budget
    F.top.rangeRestrict F.top.rangeRestrict_surjective E 2
  simpa only [MonoidHom.ker_rangeRestrict] using
    (show Nat.card (E ⊓ F.top.ker : Subgroup U) ≤
      2 * Nat.card (⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker : Subgroup U) by omega)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
