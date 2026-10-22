import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCenterCard
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import Mathlib.Algebra.CharP.Two

/-! The SAME elementary D centre has order at most two. Literal scalar
recognition and preservation of the actual Q=1 vector force its scalar
to be 1 or -1. This argument retains Q also in characteristic two and
does not assume an orthogonal-group order formula. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexCenterCard
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

theorem centerEntry_eq_one_or_neg_one (s : ℕ)
    (u : Subgroup.center (elementaryRootGroup K (s+4))) :
    centerEntry K s u=1 ∨ centerEntry K s u= -1 := by
  obtain ⟨c,hc⟩ := (elementaryRootGroup_center_iff_scalar K (s+2) u.val).mp u.property
  let v : Index (s+4)→K := Pi.single (Sum.inl 0) 1+Pi.single (Sum.inr 0) 1
  have hv : splitQuadraticForm K (s+4) v=1 := by
    simp [splitQuadraticForm_apply,splitQ,leftPart,rightPart,v,dotProduct,Pi.single_apply]
  have hact : (u.val.val : Mat K (s+4))*ᵥv=c•v := by
    rw [hc,Matrix.smul_mulVec,Matrix.one_mulVec]
  have h := elementary_preserves_bundledQ K s u.val v
  rw [hact,QuadraticMap.map_smul,hv,smul_eq_mul,mul_one] at h
  have he : centerEntry K s u=c := by
    change (u.val.val : Mat K (s+4)) (Sum.inl 0) (Sum.inl 0)=c
    simp only [hc,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
  rw [he]
  exact sq_eq_one_iff.mp (by simpa only [pow_two] using h)

def centerCode (s : ℕ) (u : Subgroup.center (elementaryRootGroup K (s+4))) : Bool := by
  classical
  exact decide (centerEntry K s u=1)

theorem centerCode_injective (s : ℕ) : Function.Injective (centerCode K s) := by
  classical
  intro u v h
  apply centerEntry_injective K s
  have he : (centerEntry K s u=1) ↔ (centerEntry K s v=1) := by
    constructor
    · intro hu
      have hv : centerCode K s v=true := h.symm.trans (by simp [centerCode,hu])
      exact of_decide_eq_true hv
    · intro hv
      have hu : centerCode K s u=true := h.trans (by simp [centerCode,hv])
      exact of_decide_eq_true hu
  rcases centerEntry_eq_one_or_neg_one K s u with hu | hu
  · exact hu.trans ((he.mp hu).symm)
  rcases centerEntry_eq_one_or_neg_one K s v with hv | hv
  · exact (he.mpr hv).trans hv.symm
  · exact hu.trans hv.symm

theorem center_card_le_two (s : ℕ) :
    Nat.card (Subgroup.center (elementaryRootGroup K (s+4)))≤2 := by
  simpa using Nat.card_le_card_of_injective (centerCode K s) (centerCode_injective K s)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality
