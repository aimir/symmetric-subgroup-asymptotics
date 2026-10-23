import SymmetricSubgroupAsymptotics.CFSGHermitianFixedProjection
import SymmetricSubgroupAsymptotics.CFSGIndependentRectangleRatio
import Mathlib.Tactic.Module

/-! A linear representative on an actual singular rectangle compares
its two mixed-ray ratios. Pointwise fixed opposed spaces determine both
components through the original Hermitian functional kernels. No
three-dimensional common-kernel argument is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

private theorem independent_sum_ne_zero {V : Type*} [AddCommGroup V] [Module K V]
    (x y : V) (h : LinearIndependent K ![x,y]) : x + y ≠ 0 := by
  intro hz
  have hc := LinearIndependent.pair_iff.mp h 1 1 (by simpa only [one_smul] using hz)
  exact one_ne_zero hc.1

private theorem sum_ne_zero_of_disjoint_components
    (P Z : Submodule K (I → K)) (hdis : Disjoint P Z)
    (x z : I → K) (hx : x ∈ P) (hz : z ∈ Z) (hx0 : x ≠ 0) : x + z ≠ 0 := by
  intro he
  have hxZ : x ∈ Z := by
    rw [add_eq_zero_iff_eq_neg.mp he]
    exact Z.neg_mem hz
  exact hx0 ((Submodule.disjoint_def.mp hdis) x hx hxZ)

theorem hermitian_rectangle_ratio_eq
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdis : Disjoint P.val Z.val)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hfixP : ∀ R : SingularPoint sigma H, R.val ≤ P.val → f R = R)
    (hfixZ : ∀ R : SingularPoint sigma H, R.val ≤ Z.val → f R = R)
    (M : IsotropicSpace sigma H) (F : SemilinearPiece sigma H f M (RingEquiv.refl K))
    (x₁ x₂ y₁ y₂ : I → K)
    (hx₁ : x₁ ∈ P.val) (hx₂ : x₂ ∈ P.val) (hy₁ : y₁ ∈ Z.val) (hy₂ : y₂ ∈ Z.val)
    (hx : LinearIndependent K ![x₁,x₂]) (hy : LinearIndependent K ![y₁,y₂])
    (hm₁ : x₁ + y₁ ∈ M.val) (hm₂ : x₂ + y₂ ∈ M.val)
    (a b t u : K) (ha : a ≠ 0)
    (he₁ : F.map ⟨x₁ + y₁, hm₁⟩ = a • (x₁ + t • y₁))
    (he₂ : F.map ⟨x₂ + y₂, hm₂⟩ = b • (x₂ + u • y₂)) : t = u := by
  have hxsum := independent_sum_ne_zero x₁ x₂ hx
  have hysum := independent_sum_ne_zero y₁ y₂ hy
  have hsum0 : (x₁ + x₂) + (y₁ + y₂) ≠ 0 :=
    sum_ne_zero_of_disjoint_components P.val Z.val hdis _ _
      (P.val.add_mem hx₁ hx₂) (Z.val.add_mem hy₁ hy₂) hxsum
  have hm : (x₁ + x₂) + (y₁ + y₂) ∈ M.val := by
    have he : (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := by module
    rw [he]
    exact M.val.add_mem hm₁ hm₂
  let w : M.val := ⟨(x₁ + x₂) + (y₁ + y₂), hm⟩
  have hw0 : w ≠ 0 := fun h => hsum0 (congrArg Subtype.val h)
  have hF0 : F.map w ≠ 0 := by
    intro h
    exact hw0 (F.injective (h.trans F.map.map_zero.symm))
  let R := singularRay sigma H w.val hsum0 (M.property w.val w.property w.val w.property)
  have hFmem : F.map w ∈ (f R).val := by
    have hp := F.ray w hw0
    rw [← singularRay_eq_projectiveInside sigma H M w hw0] at hp
    exact hp ▸ Submodule.mem_span_singleton_self (F.map w)
  have hsum : F.map w =
      (a • x₁ + b • x₂) + ((a * t) • y₁ + (b * u) • y₂) := by
    have hh := F.map.map_add (⟨x₁ + y₁, hm₁⟩ : M.val) (⟨x₂ + y₂, hm₂⟩ : M.val)
    have hew : w = (⟨x₁ + y₁, hm₁⟩ : M.val) + ⟨x₂ + y₂, hm₂⟩ := by
      apply Subtype.ext
      change (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂)
      module
    rw [hew, hh, he₁, he₂]
    module
  have himage : (a • x₁ + b • x₂) + ((a * t) • y₁ + (b * u) • y₂) ∈ (f R).val :=
    hsum ▸ hFmem
  have himage0 : (a • x₁ + b • x₂) + ((a * t) • y₁ + (b * u) • y₂) ≠ 0 := by
    rw [← hsum]
    exact hF0
  obtain ⟨c, _, hP⟩ := hermitian_fixed_projection_proportional sigma H f hf P Z hNDp hfixZ R
    (x₁ + x₂) (y₁ + y₂) (a • x₁ + b • x₂) ((a * t) • y₁ + (b * u) • y₂)
    (P.val.add_mem hx₁ hx₂) (Z.val.add_mem hy₁ hy₂)
    (P.val.add_mem (P.val.smul_mem a hx₁) (P.val.smul_mem b hx₂))
    (Z.val.add_mem (Z.val.smul_mem (a * t) hy₁) (Z.val.smul_mem (b * u) hy₂)) hxsum
    (Submodule.mem_span_singleton_self _) hsum0 himage himage0
  obtain ⟨d, _, hZ⟩ := hermitian_fixed_projection_proportional sigma H f hf Z P hNDz hfixP R
    (y₁ + y₂) (x₁ + x₂) ((a * t) • y₁ + (b * u) • y₂) (a • x₁ + b • x₂)
    (Z.val.add_mem hy₁ hy₂) (P.val.add_mem hx₁ hx₂)
    (Z.val.add_mem (Z.val.smul_mem (a * t) hy₁) (Z.val.smul_mem (b * u) hy₂))
    (P.val.add_mem (P.val.smul_mem a hx₁) (P.val.smul_mem b hx₂)) hysum
    (by simpa only [add_comm] using (Submodule.mem_span_singleton_self w.val : w.val ∈ R.val))
    (by simpa only [add_comm] using hsum0)
    (by simpa only [add_comm] using himage)
    (by simpa only [add_comm] using himage0)
  exact CFSGIndependentRectangleRatio.ratio_eq_of_two_component_comparisons
    x₁ x₂ y₁ y₂ hx hy a b c d t u ha hP hZ

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
