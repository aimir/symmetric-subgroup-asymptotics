import Mathlib.GroupTheory.Sylow

/-! A p-subgroup inside an actual H containing a global Sylow subgroup
lies in an H-conjugate of that SAME global Sylow. The witness remains
inside H; no order formula or Sylow lifting premise is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SylowSubgroupLocalContainment
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

theorem exists_conjugate_containing
    (P : Sylow p G) (H : Subgroup G) (hPH : (P : Subgroup G)≤H)
    (R : Subgroup G) (hR : IsPGroup p R) (hRH : R≤H) :
    ∃ h : H, R≤((h.val • P : Sylow p G) : Subgroup G) := by
  have hlocal : IsPGroup p (R.subgroupOf H) :=
    hR.comap_of_injective H.subtype Subtype.val_injective
  obtain ⟨Q,hRQ⟩ := hlocal.exists_le_sylow
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H (P.subtype hPH) Q
  refine ⟨h,?_⟩
  intro r hr
  have hQ : (⟨r,hRH hr⟩ : H)∈(Q : Subgroup H) := hRQ hr
  rw [←hh,Sylow.smul_subtype] at hQ
  exact hQ

end SymmetricSubgroupAsymptotics.SylowSubgroupLocalContainment
