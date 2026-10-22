import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootSubgroup
import SymmetricSubgroupAsymptotics.CFSGTypeADiagonalRootAction

/-! All nonidentity elements of the actual projective D chain-root
subgroup are conjugate. The independent third coordinate makes the
literal determinant-one torus scale the root by g, not g squared, in
every characteristic and field size. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootConjugacy
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexRootSubgroup
open CFSGOrthogonalDGenerationSLDouble CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

def scalingTorus (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 4) :=
  doubleIntoElementary K (s + 4) (CFSGTypeARootTorus.torus (first_ne_third s) g)

theorem scalingTorus_firstHom (s : ℕ) (g : Kˣ) (a : K) :
    scalingTorus K s g * firstHom K s (Multiplicative.ofAdd a) * (scalingTorus K s g)⁻¹ =
      firstHom K s (Multiplicative.ofAdd ((g : K) * a)) := by
  let D : Fin (s + 4) → K := fun k =>
    if k = first s then (g : K) else if k = third s then (g : K)⁻¹ else 1
  have hsecond : D (second s) = 1 := by
    simp only [D, if_neg (first_ne_second s).symm, if_neg (second_ne_third s)]
  have hfirst : D (first s) = (g : K) := by simp only [D, if_pos rfl]
  have hSL : CFSGTypeARootTorus.torus (first_ne_third s) g *
      elementary (first_ne_second s) a * (CFSGTypeARootTorus.torus (first_ne_third s) g)⁻¹ =
        elementary (first_ne_second s) ((g : K) * a) := by
    have h := CFSGTypeADiagonalRootAction.diagonal_conjugation
      (CFSGTypeARootTorus.torus (first_ne_third s) g) D
      (CFSGTypeARootTorus.torus_coe (first_ne_third s) g) (first_ne_second s) a
      (by rw [hsecond]; exact one_ne_zero)
    simpa only [hfirst, hsecond, div_one] using h
  change doubleIntoElementary K (s + 4) (CFSGTypeARootTorus.torus (first_ne_third s) g) *
    doubleIntoElementary K (s + 4) (elementary (first_ne_second s) a) *
      (doubleIntoElementary K (s + 4) (CFSGTypeARootTorus.torus (first_ne_third s) g))⁻¹ =
    doubleIntoElementary K (s + 4) (elementary (first_ne_second s) ((g : K) * a))
  rw [← map_inv, ← map_mul, ← map_mul, hSL]

theorem projectiveFirst_nonidentity_conjugate (s : ℕ) (a b : projectiveFirstRoot K s)
    (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ z : elementaryProjective K (s + 4),
      z * (a : elementaryProjective K (s + 4)) * z⁻¹ = b := by
  obtain ⟨u, hu⟩ := a.property
  obtain ⟨v, hv⟩ := b.property
  have hu0 : u.toAdd ≠ 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    rw [← hu, show u = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  have hv0 : v.toAdd ≠ 0 := by
    intro hz
    apply hb
    apply Subtype.ext
    rw [← hv, show v = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  let g : Kˣ := Units.mk0 (v.toAdd / u.toAdd) (div_ne_zero hv0 hu0)
  have hparam : (g : K) * u.toAdd = v.toAdd := by
    change v.toAdd / u.toAdd * u.toAdd = v.toAdd
    exact div_mul_cancel₀ _ hu0
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))
  refine ⟨pi (scalingTorus K s g), ?_⟩
  rw [← hu, ← hv]
  change pi (scalingTorus K s g) * pi (firstHom K s u) * (pi (scalingTorus K s g))⁻¹ =
    pi (firstHom K s v)
  have h := congrArg pi (scalingTorus_firstHom K s g u.toAdd)
  simpa only [map_mul, map_inv, ofAdd_toAdd, hparam] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootConjugacy
