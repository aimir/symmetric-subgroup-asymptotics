import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowTranspositionSupport
import SymmetricSubgroupAsymptotics.CFSGTwoGroupTranspositionMatching

/-! The intrinsic transposition matching of a symmetric Sylow two-subgroup.
Every point has at most one partner. The unmatched set has at most one
point, and the full normalizer preserves the resulting involution. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowCanonicalMatching
open Equiv MulAction
variable {X : Type*} [Finite X] [DecidableEq X] (P : Sylow 2 (Perm X))

def HasPartner (x : X) : Prop := ∃ y : X, y ≠ x ∧ Equiv.swap x y ∈ P

def partner (x : X) : X := if h : HasPartner P x then h.choose else x

omit [Finite X] in
theorem partner_spec {x : X} (hx : HasPartner P x) :
    partner P x ≠ x ∧ Equiv.swap x (partner P x) ∈ P := by
  simpa only [partner, dif_pos hx] using hx.choose_spec

omit [Finite X] in
theorem partner_of_not {x : X} (hx : ¬HasPartner P x) : partner P x = x :=
  dif_neg hx

theorem partner_involutive : Function.Involutive (partner P) := by
  intro x
  by_cases hx : HasPartner P x
  · obtain ⟨hne, hmem⟩ := partner_spec P hx
    have hy : HasPartner P (partner P x) :=
      ⟨x, hne.symm, by simpa only [Equiv.swap_comm] using hmem⟩
    obtain ⟨hne', hmem'⟩ := partner_spec P hy
    exact (CFSGTwoGroupTranspositionMatching.swap_partner_unique P P.isPGroup'
      hne hne'.symm (by simpa only [Equiv.swap_comm] using hmem) hmem').symm
  · rw [partner_of_not P hx, partner_of_not P hx]

def matching : Perm X := {
  toFun := partner P
  invFun := partner P
  left_inv := partner_involutive P
  right_inv := partner_involutive P }

theorem fixes_unmatched {x : X} (hx : ¬HasPartner P x) (g : P) : g • x = x := by
  by_contra h
  exact hx (CFSGSymmetricSylowTranspositionSupport.exists_swap_partner_of_moved
    P x ⟨g, h⟩)

theorem unmatched_subsingleton : {x : X | ¬HasPartner P x}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  let t : Perm X := Equiv.swap x y
  have ht : Function.Involutive t := Equiv.swap_apply_self x y
  have hc : (P : Subgroup (Perm X)) ≤ Subgroup.centralizer ({t} : Set (Perm X)) := by
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro u hu
    have hu' : u = t := Set.mem_singleton_iff.mp hu
    subst u
    change Equiv.swap x y * g = g * Equiv.swap x y
    rw [Equiv.mul_swap_eq_swap_mul,
      show g x = x from fixes_unmatched P hx ⟨g, hg⟩,
      show g y = y from fixes_unmatched P hy ⟨g, hg⟩]
  have hflips := CFSGInvolutionPairFlipGroup.flips_le_sylow t ht P hc
  have hm := hflips (CFSGInvolutionPairFlipGroup.swap_mem t ht x)
  have hm' : Equiv.swap x y ∈ P := by
    simpa only [t, Equiv.swap_apply_left] using hm
  exact hx ⟨y, Ne.symm hxy, hm'⟩

omit [Finite X] in
theorem hasPartner_image (g : Perm X)
    (hg : g ∈ Subgroup.normalizer (P : Set (Perm X))) {x : X}
    (hx : HasPartner P x) : HasPartner P (g x) := by
  obtain ⟨y, hne, hmem⟩ := hx
  have hm : g * Equiv.swap x y * g⁻¹ ∈ P :=
    ((Subgroup.mem_normalizer_iff.mp hg) (Equiv.swap x y)).mp hmem
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hm
  exact ⟨g y, fun he => hne (g.injective he), hm⟩

theorem normalizer_preserves_partner (g : Perm X)
    (hg : g ∈ Subgroup.normalizer (P : Set (Perm X))) (x : X) :
    g (partner P x) = partner P (g x) := by
  by_cases hx : HasPartner P x
  · obtain ⟨hne, hm⟩ := partner_spec P hx
    obtain ⟨hne', hm'⟩ := partner_spec P (hasPartner_image P g hg hx)
    have hconj : g * Equiv.swap x (partner P x) * g⁻¹ ∈ P :=
      ((Subgroup.mem_normalizer_iff.mp hg) _).mp hm
    rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hconj
    exact CFSGTwoGroupTranspositionMatching.swap_partner_unique P P.isPGroup'
      (fun he => hne (g.injective he).symm) hne'.symm hconj hm'
  · have hgx : ¬HasPartner P (g x) := by
      intro h
      have hh := hasPartner_image P g⁻¹
        ((Subgroup.normalizer (P : Set (Perm X))).inv_mem hg) h
      change HasPartner P (g.symm (g x)) at hh
      exact hx (by simpa only [g.symm_apply_apply] using hh)
    rw [partner_of_not P hx, partner_of_not P hgx]

theorem matching_fixedPoints_subsingleton : {x : X | matching P x = x}.Subsingleton := by
  intro x hx y hy
  apply unmatched_subsingleton P
  · intro h
    exact (partner_spec P h).1 hx
  · intro h
    exact (partner_spec P h).1 hy

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowCanonicalMatching
