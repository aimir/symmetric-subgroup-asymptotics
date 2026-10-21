import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentBorel
import SymmetricSubgroupAsymptotics.CFSGSuzukiDiagonalTorus
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Exact product coordinates for the actual Suzuki Borel envelope.
The normalization uses the proved inverse field parameter map, and every
factor remains an original unipotent or an original torus element. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGSuzukiTorus

@[simp] theorem normalizedTorus_one (m : ℕ) : normalizedTorusElement m 1 = 1 := by
  apply Units.ext
  rw [normalizedTorusElement_coe]
  simp [diagonalTorus]
  funext i
  fin_cases i <;> rfl

theorem normalizedTorus_mul (m : ℕ) (c d : (Field m)ˣ) :
    normalizedTorusElement m (c * d) = normalizedTorusElement m c * normalizedTorusElement m d := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, normalizedTorusElement_coe,
    diagonalTorus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [map_mul, mul_div_mul_comm, mul_comm]

@[simp] theorem normalizedTorus_inv (m : ℕ) (c : (Field m)ˣ) :
    (normalizedTorusElement m c)⁻¹ = normalizedTorusElement m c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← normalizedTorus_mul, mul_inv_cancel, normalizedTorus_one]

def normalizedTorusHom (m : ℕ) : (Field m)ˣ →* Ambient m where
  toFun := normalizedTorusElement m
  map_one' := normalizedTorus_one m
  map_mul' := normalizedTorus_mul m

theorem original_torus_eq_normalized (m : ℕ) (c : (Field m)ˣ) :
    ∃ d : (Field m)ˣ, torusElement m c = normalizedTorusElement m d := by
  have hi : inverseTheta m (c : Field m) ≠ 0 := by
    intro h
    apply Units.ne_zero c
    apply (inverseTheta m).injective
    simpa only [map_zero] using h
  let d : (Field m)ˣ := Units.mk0 (torusParameter m (c : Field m))
    (mul_ne_zero (Units.ne_zero c) hi)
  refine ⟨d, ?_⟩
  apply Units.ext
  rw [torusElement_coe, normalizedTorusElement_coe, original_torus_eq_diagonalTorus]
  rfl

theorem normalizedTorus_mem_borelEnvelope (m : ℕ) (c : (Field m)ˣ) :
    normalizedTorusElement m c ∈ borelEnvelope m := by
  unfold normalizedTorusElement
  exact torus_mem_borelEnvelope m _ _ rfl

theorem normalizedTorus_normalizes_unipotent (m : ℕ) :
    (normalizedTorusHom m).range ≤ Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) := by
  have hconj (c : (Field m)ˣ) (g : Ambient m) (hg : g ∈ unipotentSubgroup m) :
      normalizedTorusElement m c * g * (normalizedTorusElement m c)⁻¹ ∈ unipotentSubgroup m := by
    obtain ⟨a, b, rfl⟩ := hg
    rw [normalizedTorus_conjugation]
    exact ⟨_, _, rfl⟩
  rintro g ⟨c, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact hconj c u
  · intro hu
    change normalizedTorusElement m c * u * (normalizedTorusElement m c)⁻¹ ∈ unipotentSubgroup m at hu
    have h := hconj c⁻¹ _ hu
    simpa only [← normalizedTorus_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using h

theorem borelEnvelope_eq_unipotent_sup_torus (m : ℕ) :
    borelEnvelope m = unipotentSubgroup m ⊔ (normalizedTorusHom m).range := by
  have hUle : unipotentSubgroup m ≤ unipotentSubgroup m ⊔ (normalizedTorusHom m).range := le_sup_left
  have hTle : (normalizedTorusHom m).range ≤ unipotentSubgroup m ⊔ (normalizedTorusHom m).range := le_sup_right
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hu | ⟨c, hc⟩
    · exact hUle hu
    · have hg : g = torusElement m c := Units.ext hc
      obtain ⟨d, hd⟩ := original_torus_eq_normalized m c
      exact hTle ⟨d, (hg.trans hd).symm⟩
  · apply sup_le (unipotentSubgroup_le_borelEnvelope m)
    rintro g ⟨c, rfl⟩
    exact normalizedTorus_mem_borelEnvelope m c

/-- Every member of the SAME Borel envelope has actual U-times-T
coordinates; this is not an abstract isomorphic replacement. -/
theorem borelEnvelope_factor (m : ℕ) (g : Ambient m) (hg : g ∈ borelEnvelope m) :
    ∃ (a b : Field m) (c : (Field m)ˣ),
      g = unipotentElement m a b * normalizedTorusElement m c := by
  have hmem : g ∈ (↑(unipotentSubgroup m ⊔ (normalizedTorusHom m).range) : Set (Ambient m)) := by
    rw [← borelEnvelope_eq_unipotent_sup_torus]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (normalizedTorus_normalizes_unipotent m)] at hmem
  obtain ⟨u, hu, t, ht, hprod⟩ := hmem
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := ht
  exact ⟨a, b, c, hprod.symm⟩

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
