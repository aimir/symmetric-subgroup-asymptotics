import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter

/-! A coarse all-axis estimate when the SAME original normal lies in the
pair kernel. It forgets conditions only after retaining both joint
factors, so no quotient center is confused with the original top center. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem kernel_normal_center_card_mul_le_kernel_mul_top_center
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker) :
    Nat.card N * Nat.card (Subgroup.center (U ⧸ N)) ≤
      Nat.card F.kernelSpace * Nat.card (Subgroup.center F.top.range) := by
  let f : {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} →
      F.kernelSpace := fun v => ⟨v.val,v.property.1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun v : F.kernelSpace => v.val) h
  let g : {t : F.top.range // t ∈ Subgroup.center F.top.range ∧
      ∀ v, v ∈ F.kernelSpace → F.coordinateTopAction t v - v ∈ F.ambientAxis N} →
      Subgroup.center F.top.range := fun t => ⟨t.val,t.property.1⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun t : Subgroup.center F.top.range => t.val) h
  exact (F.kernel_normal_center_card_mul_le N hN).trans
    (Nat.mul_le_mul (Nat.card_le_card_of_injective f hf)
      (Nat.card_le_card_of_injective g hg))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
