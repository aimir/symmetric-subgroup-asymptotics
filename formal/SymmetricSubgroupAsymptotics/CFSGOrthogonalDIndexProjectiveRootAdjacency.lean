import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootProducts
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectivePlaneLabel

/-! The exact original natural root-line incidence test descends to
the ACTUAL central quotient. Specific root products and commutation lift
by common fixed vectors, not by lifting an arbitrary automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexRootDisplacements CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDIndexProjectivePlaneLabel CFSGOrthogonalDIndexProjectiveRootLift
open CFSGOrthogonalDIndexProjectiveRootProducts
variable (K : Type) [Field K]

def IsProjectiveRootElement (s : ℕ) (z : elementaryProjective K (s + 4)) : Prop :=
  ∃ x : elementaryRootGroup K (s + 4), IsRootElement s x ∧ projection K s x = z

theorem root_eq_one_of_projective_eq_one (s : ℕ)
    (x : elementaryRootGroup K (s + 4)) (hx : IsRootElement s x)
    (he : projection K s x = 1) : x = 1 := by
  obtain ⟨g, a, rfl⟩ := hx
  have hh : projection K s (g * highestRoot K s a * g⁻¹) =
      projection K s (1 * highestRoot K s 0 * (1 : elementaryRootGroup K (s + 4))⁻¹) := by
    simpa only [CFSGOrthogonalDIndexRootPlaneImage.highestRoot_zero K s,
      mul_one, one_mul, inv_one, map_one] using he
  have hu := conjugate_highestRoot_eq_of_projective_eq K s g 1 a 0 hh
  simpa only [CFSGOrthogonalDIndexRootPlaneImage.highestRoot_zero K s,
    mul_one, one_mul, inv_one] using hu

theorem projective_root_product_adjacency_iff (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hne : conjugateRootPlane K s g ≠ conjugateRootPlane K s h) :
    (∃ x ∈ projectiveConjugateRootLine K s (projection K s g), x ≠ 1 ∧
      ∃ y ∈ projectiveConjugateRootLine K s (projection K s h), y ≠ 1 ∧
        Commute x y ∧ IsProjectiveRootElement K s (x * y)) ↔
    (Module.finrank K ↥(conjugateRootPlane K s g ⊓ conjugateRootPlane K s h) = 1 ∧
      ∀ z ∈ conjugateRootPlane K s g ⊔ conjugateRootPlane K s h,
        splitQuadraticForm K (s + 4) z = 0) := by
  rw [← root_product_adjacency_iff s g h hne]
  constructor
  · rintro ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩
    rw [← map_conjugateRootLine] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff_exists s g u).mp hu
    obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff_exists s h v).mp hv
    have hun : u ≠ 1 := fun he => hxn (by rw [he, map_one])
    have hvn : v ≠ 1 := fun he => hyn (by rw [he, map_one])
    have hc' : Commute u v := by
      rw [ha, hb] at hc ⊢
      exact commute_of_projective_commute K s g h a b hc
    obtain ⟨w, ⟨k, c, hw⟩, he⟩ := hp
    have hp' : IsRootElement s (u * v) := by
      have he' : projection K s ((g * highestRoot K s a * g⁻¹) *
          (h * highestRoot K s b * h⁻¹)) = projection K s (k * highestRoot K s c * k⁻¹) := by
        rw [← ha, ← hb, ← hw, map_mul]
        exact he.symm
      exact ⟨k, c, (by rw [ha, hb]; exact product_eq_of_projective_eq K s g h k a b c he')⟩
    exact ⟨u, hu, hun, v, hv, hvn, hc', hp'⟩
  · rintro ⟨u, hu, hun, v, hv, hvn, hc, hp⟩
    have hru : IsRootElement s u := by
      obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff_exists s g u).mp hu
      exact ⟨g, a, ha⟩
    have hrv : IsRootElement s v := by
      obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff_exists s h v).mp hv
      exact ⟨h, b, hb⟩
    refine ⟨projection K s u, ?_, ?_, projection K s v, ?_, ?_, ?_, ?_⟩
    · rw [← map_conjugateRootLine]
      exact ⟨u, hu, rfl⟩
    · exact fun he => hun (root_eq_one_of_projective_eq_one K s u hru he)
    · rw [← map_conjugateRootLine]
      exact ⟨v, hv, rfl⟩
    · exact fun he => hvn (root_eq_one_of_projective_eq_one K s v hrv he)
    · change projection K s u * projection K s v = projection K s v * projection K s u
      rw [← map_mul, ← map_mul, hc.eq]
    · exact ⟨u * v, hp, (projection K s).map_mul u v⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
