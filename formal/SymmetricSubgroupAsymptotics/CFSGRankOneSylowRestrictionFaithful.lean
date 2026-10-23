import SymmetricSubgroupAsymptotics.CFSGRankOneRootOrbit
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A genuine two-cell cover makes the root subgroup transitive on the
other Sylows. For a simple group, an automorphism fixing both opposite
Sylows and the root subgroup pointwise is therefore the identity.
This avoids a separate special Weyl-word reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGRankOneSylowRestrictionFaithful
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_root_transport_sylow (P : Sylow p G) (B : Subgroup G) (w : G)
    (hBN : B = Subgroup.normalizer (P : Set G))
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : P), g = b.val * w * u.val)
    (R : Sylow p G) (hR : R ≠ P) :
    ∃ u : P, (u : G) • (w⁻¹ • P) = R := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
  have hx : (g : G ⧸ B) ≠ ((1 : G) : G ⧸ B) := by
    intro he
    have hh := QuotientGroup.eq.mp he
    have hgB : g ∈ B := by
      have hi : g⁻¹ ∈ B := by simpa only [mul_one] using hh
      simpa only [inv_inv] using B.inv_mem hi
    have hgN : g ∈ Subgroup.normalizer (P : Set G) := by rwa [← hBN]
    exact hR (hg.symm.trans (Sylow.smul_eq_iff_mem_normalizer.mpr hgN))
  obtain ⟨u, hu⟩ := CFSGRankOneRootOrbit.exists_root_transport B (P : Subgroup G) w hcover hx
  change (((u : G) * w⁻¹ : G) : G ⧸ B) = (g : G ⧸ B) at hu
  let a := ((u : G) * w⁻¹)⁻¹ * g
  have ha : a ∈ B := QuotientGroup.eq.mp hu
  have haP : a • P = P :=
    Sylow.smul_eq_iff_mem_normalizer.mpr (by rwa [← hBN])
  refine ⟨u, ?_⟩
  calc
    (u : G) • (w⁻¹ • P) = ((u : G) * w⁻¹) • P := (mul_smul _ _ _).symm
    _ = ((u : G) * w⁻¹) • (a • P) := by rw [haP]
    _ = (((u : G) * w⁻¹) * a) • P := (mul_smul _ _ _).symm
    _ = g • P := by rw [show ((u : G) * w⁻¹) * a = g by dsimp only [a]; group]
    _ = R := hg

omit [Finite G] [Fact p.Prime] in
theorem automorphism_conjugate_sylow (f : MulAut G) (g : G) (P : Sylow p G) :
    f • (g • P) = (f g) • (f • P) := by
  simp only [Sylow.smul_def]
  rw [CFSGInnerActionFaithfulness.conj_automorphism f g]
  simp only [mul_smul, inv_smul_smul]

theorem eq_one_of_fixed_root_and_opposite [IsSimpleGroup G]
    (P : Sylow p G) (B : Subgroup G) (w : G)
    (hBN : B = Subgroup.normalizer (P : Set G)) (hw : w ∉ B)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : P), g = b.val * w * u.val)
    (f : MulAut G) (hfP : f • P = P) (hfQ : f • (w⁻¹ • P) = w⁻¹ • P)
    (hfix : ∀ u : P, f u.val = u.val) : f = 1 := by
  let pi := MulAction.toPermHom (MulAut G) (Sylow p G)
  have hpi : Function.Injective pi :=
    CFSGInnerActionFaithfulness.injective_of_inner_nontrivial pi (by
      refine ⟨w, ?_⟩
      intro he
      have hh := congrArg (fun e : Equiv.Perm (Sylow p G) => e P) he
      change (MulAut.conj w) • P = P at hh
      apply hw
      rw [hBN]
      exact Sylow.smul_eq_iff_mem_normalizer.mp hh)
  apply hpi
  apply Equiv.ext
  intro R
  change f • R = (1 : MulAut G) • R
  rw [one_smul]
  by_cases hR : R = P
  · subst R
    exact hfP
  · obtain ⟨u, rfl⟩ := exists_root_transport_sylow P B w hBN hcover R hR
    rw [automorphism_conjugate_sylow, hfix u, hfQ]

end SymmetricSubgroupAsymptotics.CFSGRankOneSylowRestrictionFaithful
