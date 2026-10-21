import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowActions
import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.NormNum

/-! An actual nonidentity binary linear element extends the same regular
translation subgroup to a larger actual transitive binary subgroup. This
retains point actions and uses no subgroup-order classification. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineBinaryExtensions
open BinaryThreeAffineRowActions

abbrev H : Subgroup Ambient := translation.range

theorem translation_injective : Function.Injective translation := by
  intro v w h
  apply points.injective
  have he := Equiv.congr_fun h (points 1)
  simpa only [translation_apply,mul_one] using he

theorem card_translation : Nat.card H = 8 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective translation_injective).toEquiv]
  simp [Translation,BinaryThreeAffineRowActions.Vector,Nat.card_eq_fintype_card]

theorem translation_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 3) card_translation

theorem translation_transitive : PermutationSubgroupTransitive H := by
  intro x y
  obtain ⟨v,rfl⟩ := points.surjective x
  obtain ⟨w,rfl⟩ := points.surjective y
  refine ⟨translation (w*v⁻¹),⟨w*v⁻¹,rfl⟩,?_⟩
  rw [translation_apply,inv_mul_cancel_right]

theorem linear_normalizes (c : Linear) : linear c ∈ Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun K : Subgroup Ambient => (K : Set Ambient))
    (linear_conjugate_translations c)

theorem linear_not_translation (c : Linear) (hc : c ≠ 1) : linear c ∉ H := by
  rintro ⟨v,hv⟩
  have he := Equiv.congr_fun hv (points 1)
  rw [translation_apply,mul_one,linear_apply,map_one] at he
  have hv1 : v = 1 := points.injective he
  apply hc
  apply GeneralThreeTwoPointAction.action_injective
  simpa only [hv1,map_one] using hv.symm

theorem contains_above (K : Subgroup Linear) (c : Linear) (hcK : c ∈ K)
    (k : ℕ) (hpow : c ^ (2 ^ k) = 1) (hc : c ≠ 1) :
    PermutationPrimePowerSeedEscape.ContainsAbove 2 8 (affine K) := by
  let P : Subgroup Ambient := H ⊔ Subgroup.zpowers (linear c)
  have hpow' : linear c ^ (2 ^ k) = 1 := by rw [←map_pow,hpow,map_one]
  have hP : IsPGroup 2 P :=
    FiniteNormalizerPElementExtension.extension_isPGroup H translation_isPGroup
      (linear c) k hpow' (linear_normalizes c)
  have hPA : P ≤ affine K :=
    FiniteNormalizerPElementExtension.extension_le H (affine K) le_sup_left
      (linear c) ((show K.map linear ≤ affine K from le_sup_right) ⟨c,hcK,rfl⟩)
  refine ⟨P,hPA,hP,permutationSubgroupTransitive_mono H P le_sup_left
    translation_transitive,?_⟩
  exact card_translation.symm.trans_lt
    (FiniteNormalizerPElementExtension.card_lt_extension H (linear c)
      (linear_not_translation c hc))

end SymmetricSubgroupAsymptotics.BinaryThreeAffineBinaryExtensions
end
