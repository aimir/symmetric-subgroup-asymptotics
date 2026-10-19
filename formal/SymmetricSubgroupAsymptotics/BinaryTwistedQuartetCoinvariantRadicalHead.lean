import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalHead
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalSubmodules

/-! Genuine V4 coinvariant quotients of arbitrary invariant binary
radical subspaces have at most ONE nontrivial cubic slot. The constant
annihilation needed by the rank factorization is proved from the actual
V4 operators; it is not an extra head-capacity premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantRadicalHead
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations

private theorem cubic_spans : ∀ u v : Plane, u≠0 →
    ∃ a b : Bit, v=a • u+b • cubic u := by decide +kernel
private theorem add_self {Q : Type} [AddCommGroup Q] [Module Bit Q] (x : Q) : x+x=0 := by
  rw [← two_smul Bit,show (2 : Bit)=0 by decide,zero_smul]

variable (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hflip : ∀ v, v∈W → flipAction v∈W)
    (hsecond : ∀ v, v∈W → secondFlip v∈W)
    (hrad : ∀ v, v∈W → sumBlocks v=0)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (T : Module.End Bit Q)
    (hinter : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=T (q v))
    (hqflip : ∀ v : W, q ⟨flipAction v,hflip v v.property⟩=q v)
    (hqsecond : ∀ v : W, q ⟨secondFlip v,hsecond v v.property⟩=q v)

include hcycle hflip hsecond hrad hinter hqflip hqsecond in
theorem kills_constants_of_nonconstant
    (v : W) (hnon : v.val≠constant (v.val 0)) :
    ∀ w : W, w.val=constant (w.val 0) → q w=0 := by
  have hall : ∀ u : Plane, constant u∈W :=
    BinaryTwistedQuartetRadicalSubmodules.all_constants_of_nonconstant_radical
      W hcycle hflip hsecond v v.property (hrad v v.property) hnon
  let c : Plane →ₗ[Bit] W := {
    toFun u := ⟨constant u,hall u⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let f := q.comp c
  have hc : ∀ u, f (cubic u)=T (f u) := by
    intro u
    have hh := hinter (c u)
    have he : (⟨cycleAction (c u),hcycle (c u) (c u).property⟩ : W)=c (cubic u) :=
      Subtype.ext (cycle_constant u)
    rw [he] at hh
    exact hh
  have hu : v.val 0+v.val 3≠0 ∨ v.val 0+v.val 2≠0 := by
    by_contra h
    push_neg at h
    have hf : flipAction v.val=v.val := by
      apply add_left_cancel (a := v.val)
      rw [flip_radical v.val (hrad v v.property),h.1]
      exact (add_self v.val).symm
    have hs : secondFlip v.val=v.val := by
      apply add_left_cancel (a := v.val)
      rw [second_radical v.val (hrad v v.property),h.2]
      exact (add_self v.val).symm
    exact hnon (common_fixed_constant v.val hf hs)
  have hz : ∃ u : Plane, u≠0 ∧ f u=0 := by
    rcases hu with hu | hu
    · refine ⟨v.val 0+v.val 3,hu,?_⟩
      have he : c (v.val 0+v.val 3)=v+⟨flipAction v,hflip v v.property⟩ :=
        Subtype.ext (flip_radical v.val (hrad v v.property)).symm
      change q (c _)=0
      rw [he,map_add,hqflip]
      exact add_self _
    · refine ⟨v.val 0+v.val 2,hu,?_⟩
      have he : c (v.val 0+v.val 2)=v+⟨secondFlip v,hsecond v v.property⟩ :=
        Subtype.ext (second_radical v.val (hrad v v.property)).symm
      change q (c _)=0
      rw [he,map_add,hqsecond]
      exact add_self _
  obtain ⟨u,hun,huz⟩ := hz
  have hbu : f (cubic u)=0 := by rw [hc,huz,map_zero]
  have hfzero : ∀ z : Plane, f z=0 := by
    intro z
    obtain ⟨a,b,hz⟩ := cubic_spans u z hun
    rw [hz,map_add,map_smul,map_smul,huz,hbu,smul_zero,smul_zero,add_zero]
  intro w hw
  have he : c (w.val 0)=w := Subtype.ext hw.symm
  rw [← he]
  exact hfzero _

include hcycle hflip hsecond hrad hinter hqflip hqsecond in
theorem nontrivial_rank_le_two (hq : Function.Surjective q) :
    Module.finrank Bit (LinearMap.range (T+T^2))≤2 := by
  by_cases hconst : ∀ v : W, v.val=constant (v.val 0)
  · let ev : W →ₗ[Bit] Plane := (LinearMap.proj 0).comp W.subtype
    have hev : Function.Injective ev := by
      intro v w h
      apply Subtype.ext
      exact (hconst v).trans ((congrArg constant h).trans (hconst w).symm)
    have hw : Module.finrank Bit W≤2 :=
      (ev.finrank_le_finrank_of_injective hev).trans (by simp [Plane])
    letI : FiniteDimensional Bit Q := FiniteDimensional.of_surjective q hq
    exact (T+T^2).range.finrank_le.trans
      ((LinearMap.finrank_le_finrank_of_surjective hq).trans hw)
  · push_neg at hconst
    obtain ⟨v,hv⟩ := hconst
    exact BinaryTwistedQuartetRadicalHead.nontrivial_rank_le_two W hcycle hrad q hq T
      hinter (kills_constants_of_nonconstant W hcycle hflip hsecond hrad q T
        hinter hqflip hqsecond v hv)

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantRadicalHead
