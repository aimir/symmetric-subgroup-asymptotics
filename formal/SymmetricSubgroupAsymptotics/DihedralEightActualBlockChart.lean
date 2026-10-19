import SymmetricSubgroupAsymptotics.DihedralEightFourPointImage
import SymmetricSubgroupAsymptotics.PermutationConjugateTopChart

/-! Exact D8 group and physical block charts for every actual order-eight
four-point top. Both charts come from the same Sylow conjugator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralEightActualBlockChart
open DihedralEightRegularKleinBlockModel DihedralEightFourPointImage

private theorem image_inverse (d : actionFin.range) :
    actionFin (imageEquiv.symm d)=(d : Equiv.Perm (Fin 4)) :=
  congrArg Subtype.val (imageEquiv.apply_symm_apply d)

/-- The point chart intertwines the original block action with the checked
D8 action, so the original affine subgroup can be transported exactly. -/
theorem exists_chart (B : Subgroup (Equiv.Perm (Fin 4)))
    (hB : Nat.card B=8) :
    ∃ e : B ≃* Q, ∃ c : Fin 4 ≃ R,
      ∀ b : B, ∀ i : Fin 4, c (b • i)=e b • c i := by
  obtain ⟨g,hg⟩ := DihedralEightFourPointImage.exists_conjugator B hB
  let E := PermutationConjugateTopChart.groupChart B actionFin.range g hg
  let e : B ≃* Q := E.trans imageEquiv.symm
  let c : Fin 4 ≃ R := g.trans label.symm
  refine ⟨e,c,?_⟩
  intro b i
  apply label.injective
  change label (label.symm (g (b • i)))=label
    (imageEquiv.symm (E b) • label.symm (g i))
  rw [label.apply_symm_apply]
  change g (b • i)=label (imageEquiv.symm (E b) • label.symm (g i))
  rw [← actionFin_label, label.apply_symm_apply, image_inverse]
  exact PermutationConjugateTopChart.equivariant B actionFin.range g hg b i
end SymmetricSubgroupAsymptotics.DihedralEightActualBlockChart
