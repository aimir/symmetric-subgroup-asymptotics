import SymmetricSubgroupAsymptotics.CFSGGTwoOpposedFlagIntersection

/-! Unique U6*T2 and B6*w0*U6 factors in the actual original G2 model.
These are injectivity statements, proved from the actual native complete flag;
no surjectivity of fixed points or classification of a fixed group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBigCellUniqueness
open CFSGGTwoSerreMatrices CFSGGTwoNaturalBruhatFlag CFSGMatrixFlagSubgroups
open CFSGGTwoOriginalBruhatUniqueness CFSGGTwoOpposedFlagIntersection
open CFSGGTwoPositiveWordSubgroup CFSGGTwoOriginalBorel
open CFSGGTwoOriginalRankTwoTorus CFSGReeGTwoOriginalOpposition
variable (K : Type) [Field K] [CharP K 3]
local notation "G" => CFSG.Models.Chevalley.Model CartanMatrix.G₂ K

theorem positive_torus_intersection (g : G)
    (hu : g∈positiveWordGroup K) (ht : g∈torus K) : g=1 := by
  apply nativeHom_injective K
  rw [map_one]
  have hdiag := (native_positive_unipotent K g hu).2
  obtain ⟨t,rfl⟩ := ht
  rw [torusHom_apply,nativeHom_torus] at hdiag ⊢
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (↑(CFSGGTwoNaturalRankTwoTorus.torusPair K t).val : Mat K) i j=(1 : Mat K) i j
  by_cases h : i=j
  · subst j
    exact (hdiag i).trans (Matrix.one_apply_eq i).symm
  · rw [torusPair_diagonal]
    simp only [Matrix.diagonal_apply,Matrix.one_apply,if_neg h]

private theorem product_unique {H : Type*} [Group H] (U T : Subgroup H)
    (hinter : ∀ g∈U,g∈T → g=1)
    (u1 u2 t1 t2 : H) (hu1 : u1∈U) (hu2 : u2∈U)
    (ht1 : t1∈T) (ht2 : t2∈T) (he : u1*t1=u2*t2) : u1=u2 ∧ t1=t2 := by
  have hx : u2⁻¹*u1=t2*t1⁻¹ := by
    calc
      _=u2⁻¹*(u1*t1)*t1⁻¹ := by group
      _=u2⁻¹*(u2*t2)*t1⁻¹ := by rw [he]
      _=_ := by group
  have h1 : u2⁻¹*u1=1 := hinter _ (U.mul_mem (U.inv_mem hu2) hu1)
    (hx.symm ▸ T.mul_mem ht2 (T.inv_mem ht1))
  have hu : u1=u2 := (inv_mul_eq_one.mp h1).symm
  refine ⟨hu,?_⟩
  rw [hu] at he
  exact mul_left_cancel he

theorem positive_torus_factors_unique
    (u1 u2 t1 t2 : G) (hu1 : u1∈positiveWordGroup K) (hu2 : u2∈positiveWordGroup K)
    (ht1 : t1∈torus K) (ht2 : t2∈torus K) (he : u1*t1=u2*t2) :
    u1=u2 ∧ t1=t2 :=
  product_unique (positiveWordGroup K) (torus K) (positive_torus_intersection K)
    u1 u2 t1 t2 hu1 hu2 ht1 ht2 he

private theorem big_cell_rearrange {H : Type*} [Group H]
    (b1 b2 w u1 u2 : H) (he : b1*w*u1=b2*w*u2) :
    w*(u1*u2⁻¹)*w⁻¹=b1⁻¹*b2 := by
  calc
    _=b1⁻¹*(b1*w*u1)*u2⁻¹*w⁻¹ := by group
    _=b1⁻¹*(b2*w*u2)*u2⁻¹*w⁻¹ := by rw [he]
    _=_ := by group

theorem borel_opposition_positive_factors_unique
    (b1 b2 u1 u2 : G) (hb1 : b1∈borel K) (hb2 : b2∈borel K)
    (hu1 : u1∈positiveWordGroup K) (hu2 : u2∈positiveWordGroup K)
    (he : b1*longestWord K*u1=b2*longestWord K*u2) : b1=b2 ∧ u1=u2 := by
  have hx := big_cell_rearrange b1 b2 (longestWord K) u1 u2 he
  have h1 : u1*u2⁻¹=1 := original_opposed_positive_intersection K _
    ((positiveWordGroup K).mul_mem hu1 ((positiveWordGroup K).inv_mem hu2))
    (hx.symm ▸ (borel K).mul_mem ((borel K).inv_mem hb1) hb2)
  have hu : u1=u2 := mul_inv_eq_one.mp h1
  refine ⟨?_,hu⟩
  rw [hu] at he
  exact mul_right_cancel (mul_right_cancel he)

theorem positive_torus_opposition_positive_factors_unique
    (u1 u2 t1 t2 v1 v2 : G)
    (hu1 : u1∈positiveWordGroup K) (hu2 : u2∈positiveWordGroup K)
    (ht1 : t1∈torus K) (ht2 : t2∈torus K)
    (hv1 : v1∈positiveWordGroup K) (hv2 : v2∈positiveWordGroup K)
    (he : u1*t1*longestWord K*v1=u2*t2*longestWord K*v2) :
    u1=u2 ∧ t1=t2 ∧ v1=v2 := by
  have h := borel_opposition_positive_factors_unique K (u1*t1) (u2*t2) v1 v2
    ((borel K).mul_mem (positive_le_borel K hu1) (torus_le_borel K ht1))
    ((borel K).mul_mem (positive_le_borel K hu2) (torus_le_borel K ht2)) hv1 hv2 he
  have h' := positive_torus_factors_unique K u1 u2 t1 t2 hu1 hu2 ht1 ht2 h.1
  exact ⟨h'.1,h'.2,h.2⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBigCellUniqueness
