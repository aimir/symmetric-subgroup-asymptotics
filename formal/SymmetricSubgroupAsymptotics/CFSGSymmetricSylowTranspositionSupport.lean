import SymmetricSubgroupAsymptotics.CFSGTransitiveTwoGroupCentralMatching
import SymmetricSubgroupAsymptotics.CFSGInvolutionPairFlipGroup
import Mathlib.GroupTheory.GroupAction.Defs

/-! Every point moved by a symmetric Sylow two-subgroup belongs to a
transposition of that SAME subgroup. Restrict to its actual orbit, take a
central involution of the faithful image, extend by the identity, and use
Sylow maximality to include its pair flips. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowTranspositionSupport
open Equiv MulAction

theorem exists_swap_partner_of_moved
    {X : Type*} [Finite X] [DecidableEq X] (P : Sylow 2 (Perm X)) (x : X)
    (hx : ∃ g : P, g • x ≠ x) : ∃ y : X, y ≠ x ∧ Equiv.swap x y ∈ P := by
  let O := MulAction.orbit P x
  let rho : P →* Perm O := MulAction.toPermHom P O
  let H : Subgroup (Perm O) := rho.range
  letI : Nontrivial O := by
    obtain ⟨g, hg⟩ := hx
    refine ⟨⟨⟨g • x, MulAction.mem_orbit x g⟩, ⟨x, MulAction.mem_orbit_self x⟩, ?_⟩⟩
    intro he
    exact hg (congrArg Subtype.val he)
  letI : IsPretransitive H O := by
    constructor
    intro a b
    obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    refine ⟨rho.rangeRestrict (v * u⁻¹), ?_⟩
    apply Subtype.ext
    change (v * u⁻¹) • (a : X) = (b : X)
    rw [← hu, mul_smul, inv_smul_smul]
    exact hv
  letI : Nontrivial H := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne O
    obtain ⟨g, hg⟩ := exists_smul_eq H a b
    refine ⟨⟨g, 1, ?_⟩⟩
    intro he
    subst g
    exact hab (by simpa only [one_smul] using hg)
  have hH : IsPGroup 2 H := P.isPGroup'.of_surjective rho.rangeRestrict
    rho.rangeRestrict_surjective
  obtain ⟨z, hz, hsq, hfree⟩ :=
    CFSGTransitiveTwoGroupCentralMatching.exists_fixed_point_free_involution
      (X := O) hH
  let t : Perm O := z.val
  let tau : Perm X := Perm.ofSubtype t
  have ht : Function.Involutive t := by
    intro a
    have he := congrArg (fun u : H => u.val a) hsq
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one,
      Perm.mul_apply, Perm.one_apply] using he
  have htau : Function.Involutive tau := by
    intro a
    by_cases ha : a ∈ O
    · change Perm.ofSubtype t (Perm.ofSubtype t a) = a
      rw [Perm.ofSubtype_apply_of_mem _ ha,
        Perm.ofSubtype_apply_of_mem _ (t ⟨a, ha⟩).property]
      exact congrArg Subtype.val (ht ⟨a, ha⟩)
    · change Perm.ofSubtype t (Perm.ofSubtype t a) = a
      rw [Perm.ofSubtype_apply_of_not_mem _ ha, Perm.ofSubtype_apply_of_not_mem _ ha]
  have hc : (P : Subgroup (Perm X)) ≤ Subgroup.centralizer ({tau} : Set (Perm X)) := by
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro u hu
    have hu' : u = tau := Set.mem_singleton_iff.mp hu
    subst u
    apply Perm.ext
    intro a
    change tau (g a) = g (tau a)
    by_cases ha : a ∈ O
    · have hga : g a ∈ O := mapsTo_smul_orbit (⟨g, hg⟩ : P) x ha
      have he := congrArg (fun v : H => (v.val : Perm O) ⟨a, ha⟩)
        (Subgroup.mem_center_iff.mp hz (rho.rangeRestrict ⟨g, hg⟩))
      have he' := congrArg Subtype.val he
      change g (t ⟨a, ha⟩).val = (t ⟨g a, hga⟩).val at he'
      change Perm.ofSubtype t (g a) = g (Perm.ofSubtype t a)
      rw [Perm.ofSubtype_apply_of_mem _ hga, Perm.ofSubtype_apply_of_mem _ ha]
      exact he'.symm
    · have hga : g a ∉ O := by
        intro hm
        have hh := mapsTo_smul_orbit (⟨g, hg⟩ : P)⁻¹ x hm
        apply ha
        change (⟨g, hg⟩ : P)⁻¹ • ((⟨g, hg⟩ : P) • a) ∈ O at hh
        simpa only [inv_smul_smul] using hh
      change Perm.ofSubtype t (g a) = g (Perm.ofSubtype t a)
      rw [Perm.ofSubtype_apply_of_not_mem _ hga, Perm.ofSubtype_apply_of_not_mem _ ha]
  have hflips := CFSGInvolutionPairFlipGroup.flips_le_sylow tau htau P hc
  refine ⟨tau x, ?_, hflips (CFSGInvolutionPairFlipGroup.swap_mem tau htau x)⟩
  intro he
  apply hfree (⟨x, MulAction.mem_orbit_self x⟩ : O)
  apply Subtype.ext
  change (t ⟨x, MulAction.mem_orbit_self x⟩).val = x
  simpa only [tau, Perm.ofSubtype_apply_of_mem t (MulAction.mem_orbit_self x)] using he

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowTranspositionSupport
