import SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointCount
import SymmetricSubgroupAsymptotics.CFSGGTwoLongRootVectorActions
import Mathlib.LinearAlgebra.Projectivization.Action

/-! The literal natural group acts on singular rays in its invariant
seven-space. An actual long-root word moves a specified singular ray. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointAction
open CFSGGTwoSerreMatrices CFSGGTwoAxisCoordinates CFSGGTwoSingularPointCount
open CFSGGTwoD4Inclusion CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def hyperplaneLinearEquiv (g : naturalGroup K) : axisHyperplane K ≃ₗ[K] axisHyperplane K where
  toFun v := ⟨(g.val : Mat K) *ᵥ v.val, natural_preserves_hyperplane K g v⟩
  invFun v := ⟨(↑(g⁻¹).val : Mat K) *ᵥ v.val, natural_preserves_hyperplane K g⁻¹ v⟩
  left_inv v := by
    apply Subtype.ext
    change (↑(g⁻¹).val : Mat K) *ᵥ ((g.val : Mat K) *ᵥ v.val) = v.val
    have he : (↑(g⁻¹).val : Mat K) * (g.val : Mat K) = 1 :=
      congrArg (fun u : naturalGroup K => (u.val : Mat K)) (inv_mul_cancel g)
    rw [Matrix.mulVec_mulVec, he, Matrix.one_mulVec]
  right_inv v := by
    apply Subtype.ext
    change (g.val : Mat K) *ᵥ ((↑(g⁻¹).val : Mat K) *ᵥ v.val) = v.val
    have he : (g.val : Mat K) * (↑(g⁻¹).val : Mat K) = 1 :=
      congrArg (fun u : naturalGroup K => (u.val : Mat K)) (mul_inv_cancel g)
    rw [Matrix.mulVec_mulVec, he, Matrix.one_mulVec]
  map_add' v w := by
    apply Subtype.ext
    change (g.val : Mat K) *ᵥ (v.val + w.val) = _
    exact Matrix.mulVec_add _ _ _
  map_smul' a v := by
    apply Subtype.ext
    change (g.val : Mat K) *ᵥ (a • v.val) = a • ((g.val : Mat K) *ᵥ v.val)
    exact Matrix.mulVec_smul _ _ _

theorem hyperplaneLinearEquiv_apply (g : naturalGroup K) (v : axisHyperplane K) :
    (hyperplaneLinearEquiv K g v).val = (g.val : Mat K) *ᵥ v.val := rfl

def hyperplaneLinearHom : naturalGroup K →* (axisHyperplane K ≃ₗ[K] axisHyperplane K) where
  toFun := hyperplaneLinearEquiv K
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change (1 : Mat K) *ᵥ v.val = v.val
    exact Matrix.one_mulVec _
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change ((g.val : Mat K) * (h.val : Mat K)) *ᵥ v.val =
      (g.val : Mat K) *ᵥ ((h.val : Mat K) *ᵥ v.val)
    exact (Matrix.mulVec_mulVec _ _ _).symm

theorem hyperplane_preserves_Q (g : naturalGroup K) (v : axisHyperplane K) :
    axisQuadraticForm K (hyperplaneLinearHom K g v) = axisQuadraticForm K v := by
  change splitQuadraticForm K 4 ((g.val : Mat K) *ᵥ v.val) = splitQuadraticForm K 4 v.val
  exact natural_preserves_Q K g v.val

abbrev pointAction : MulAction (naturalGroup K) (Projectivization K (axisHyperplane K)) :=
  MulAction.compHom _ (hyperplaneLinearHom K)

theorem singular_mk (v : axisHyperplane K) (hv : v ≠ 0) (hQ : axisQuadraticForm K v = 0) :
    Projectivization.mk K v hv ∈ singularPoints K := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  change axisQuadraticForm K (Projectivization.mk K v hv).rep = 0
  rw [←ha]
  change axisQuadraticForm K ((a : K) • v) = 0
  rw [QuadraticMap.map_smul, hQ, smul_zero]

theorem point_preserves_singular (g : naturalGroup K)
    (p : Projectivization K (axisHyperplane K)) (hp : p ∈ singularPoints K) :
    letI := pointAction K
    g • p ∈ singularPoints K := by
  letI := pointAction K
  change (hyperplaneLinearHom K g) • p ∈ singularPoints K
  have hne : hyperplaneLinearHom K g p.rep ≠ 0 := by
    intro h
    apply p.rep_nonzero
    apply (hyperplaneLinearHom K g).injective
    exact h.trans (map_zero (hyperplaneLinearHom K g)).symm
  have he : (hyperplaneLinearHom K g) • p =
      Projectivization.mk K (hyperplaneLinearHom K g p.rep) hne := by
    conv_lhs => rw [←Projectivization.mk_rep p, Projectivization.smul_mk]
    rfl
  rw [he]
  apply singular_mk
  exact (hyperplane_preserves_Q K g p.rep).trans hp

def movedVector : axisHyperplane K :=
  ⟨Pi.single (pos 2) 1, by simp [axisHyperplane, pos, neg, Fin.ext_iff]⟩

theorem movedVector_ne_zero : movedVector K ≠ 0 := by
  intro h
  have he := congrArg (fun v : axisHyperplane K => v.val (pos 2)) h
  simpa [movedVector] using he

def movedPoint : Projectivization K (axisHyperplane K) :=
  Projectivization.mk K (movedVector K) (movedVector_ne_zero K)

theorem movedPoint_singular : movedPoint K ∈ singularPoints K := by
  apply singular_mk
  change splitQuadraticForm K 4 (Pi.single (pos 2) 1) = 0
  rw [splitQuadraticForm_apply]
  simp [CFSGOrthogonalDIndexQuadraticForm.splitQ, CFSGOrthogonalDIndexQuadraticForm.leftPart,
    CFSGOrthogonalDIndexQuadraticForm.rightPart, dotProduct, pos, neg]

theorem long_root_moves_point :
    letI := pointAction K
    naturalRoot K false 1 1 • movedPoint K ≠ movedPoint K := by
  letI := pointAction K
  change (hyperplaneLinearHom K (naturalRoot K false 1 1)) •
    Projectivization.mk K (movedVector K) (movedVector_ne_zero K) ≠ _
  rw [Projectivization.smul_mk]
  intro he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp he
  have hh := congrArg (fun v : axisHyperplane K => v.val (pos 1)) ha
  change a * (movedVector K).val (pos 1) =
    ((rootTransvection K false 1 1 : Mat K) *ᵥ (movedVector K).val) (pos 1) at hh
  rw [CFSGGTwoLongRootVectorActions.positive_apply] at hh
  simpa [movedVector, CFSGGTwoLongRootVectorActions.positiveAction, pos, neg, Fin.ext_iff] using hh

end SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointAction
