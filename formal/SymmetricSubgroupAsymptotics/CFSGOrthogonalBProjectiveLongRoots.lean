import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveEquiv

/-! Intrinsic long-root recognition on the actual full-centre quotient.
The literal quotient map is an isomorphism by the checked odd-B centre
calculation; no lifting assumption on projective automorphisms is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

def IsProjectiveLongRootElement (s : ℕ) (x : elementaryProjective K (s + 3)) : Prop :=
  ∃ g : elementaryRootGroup K (s + 3), ∃ a : K,
    x = QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))
      (g * highestRoot s a * g⁻¹)

theorem isProjectiveLongRootElement_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (x : elementaryProjective K (s + 3)) :
    IsProjectiveLongRootElement s x ↔
      IsLongRootElement s ((oddProjectiveEquiv K p h2 (s + 2)).symm x) := by
  let e := oddProjectiveEquiv K p h2 (s + 2)
  constructor
  · rintro ⟨g, a, hx⟩
    change x = e (g * highestRoot s a * g⁻¹) at hx
    refine ⟨g, a, ?_⟩
    rw [hx, e.symm_apply_apply]
  · rintro ⟨g, a, hx⟩
    refine ⟨g, a, ?_⟩
    change e.symm x = g * highestRoot s a * g⁻¹ at hx
    change x = e (g * highestRoot s a * g⁻¹)
    have he := congrArg e hx
    simpa only [e.apply_symm_apply] using he

theorem automorphism_isProjectiveLongRootElement_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (x : elementaryProjective K (s + 3)) :
    IsProjectiveLongRootElement s (f x) ↔ IsProjectiveLongRootElement s x := by
  let e := oddProjectiveEquiv K p h2 (s + 2)
  let fE : MulAut (elementaryRootGroup K (s + 3)) := e.trans (f.trans e.symm)
  rw [isProjectiveLongRootElement_iff p h2, isProjectiveLongRootElement_iff p h2]
  have h := automorphism_isLongRootElement_iff p h2 s fE (e.symm x)
  simpa only [fE, MulEquiv.trans_apply, e.apply_symm_apply] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
