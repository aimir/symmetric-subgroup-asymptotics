import SymmetricSubgroupAsymptotics.QuotientCenterProjectionCard
import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel

/-! A quotient centre can retain nontrivial top elements. Its size is
bounded jointly by the actual fixed kernel vectors and the top elements
acting trivially on that kernel modulo the SAME original normal axis.
Arbitrary affine lift errors remain retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem quotient_center_card_mul_le_coordinate_product
    (A : Subrepresentation F.coordinateTopAction)
    (hA : A.toSubmodule ≤ F.kernelSpace) :
    Nat.card A.toSubmodule *
        Nat.card (Subgroup.center (U ⧸ F.coordinateSubgroup A.toSubmodule)) ≤
      Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
        ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ A.toSubmodule} *
      Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
        F.coordinateTopAction t v - v ∈ A.toSubmodule} := by
  let N := F.coordinateSubgroup A.toSubmodule
  let K := binaryPairFixedSubgroup F.top.ker N
  let T : F.top.range → Prop := fun t => ∀ v, v ∈ F.kernelSpace →
    F.coordinateTopAction t v - v ∈ A.toSubmodule
  have hb := QuotientCenterProjectionCard.card_mul_le N
    F.top.rangeRestrict K T
    (fun g hg hc => ⟨congrArg Subtype.val hg, hc⟩)
    (by
      intro g hg v hv
      obtain ⟨k, hk⟩ := hv
      change F.bits k.toMul = v at hk
      rw [← hk]
      exact F.central_quotient_displacement A g hg k.toMul)
  let k : K → {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ A.toSubmodule} := fun x =>
    let u : F.top.ker := ⟨x.val, x.property.1⟩
    ⟨F.bits u, ⟨⟨Additive.ofMul u, rfl⟩,
      (F.kernel_mem_coordinate_fixed A u).mp x.property⟩⟩
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    have he : (⟨x.val, x.property.1⟩ : F.top.ker) = ⟨y.val, y.property.1⟩ := by
      apply F.bitsHom_injective
      exact congrArg Multiplicative.ofAdd (congrArg Subtype.val h)
    exact congrArg (fun z : F.top.ker => (z : U)) he
  rw [F.coordinateSubgroup_card A.toSubmodule hA] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective k hk))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
