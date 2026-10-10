import SymmetricSubgroupAsymptotics.FiniteTwoNormalSocleGenerators
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# One socle generator along a three-point normal chain

A small finite catalogue row often proves that the complete normal lattice is
`⊥ < E < ⊤`.  This file converts exactly that checked statement into the three
one-position socle witnesses needed by the bottom, middle, and top quotient
rows.  No identification with a named finite group is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The reusable information extracted from a checked three-state normal
registry.  The distinguished element gives a literal normal generator of the
unique proper nontrivial normal subgroup. -/
structure FiniteThreeNormalChainData (G : Type) [Group G] where
  middle : Subgroup G
  middle_normal : middle.Normal
  middle_ne_bot : middle ≠ ⊥
  middle_ne_top : middle ≠ ⊤
  normal_eq_bot_or_middle_or_top :
    ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = middle ∨ N = ⊤
  generator : G
  generator_mem : generator ∈ middle
  generator_ne_one : generator ≠ 1

attribute [instance] FiniteThreeNormalChainData.middle_normal

namespace FiniteThreeNormalChainData

variable {G H : Type} [Group G] [Group H]
variable (D : FiniteThreeNormalChainData G)

/-- The distinguished literal element normally generates the middle state. -/
theorem normalClosure_generator_eq_middle :
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ D.generator)) =
      D.middle := by
  have hle :
      Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ D.generator)) ≤
        D.middle := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact D.generator_mem
  rcases D.normal_eq_bot_or_middle_or_top
      (Subgroup.normalClosure
        (Set.range (fun _ : Fin 1 ↦ D.generator))) (by infer_instance) with
      hbot | hmiddle | htop
  · exfalso
    apply D.generator_ne_one
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
  · exact hmiddle
  · exfalso
    apply D.middle_ne_top
    exact top_unique (by simpa only [htop] using hle)

/-- The middle state is the unique minimal normal subgroup. -/
theorem middle_isMinimalNormalSubgroup :
    IsMinimalNormalSubgroup D.middle := by
  refine ⟨inferInstance, D.middle_ne_bot, ?_⟩
  intro N hN hNne hNle
  rcases D.normal_eq_bot_or_middle_or_top N hN with hbot | hmiddle | htop
  · exact (hNne hbot).elim
  · exact hmiddle
  · exfalso
    apply D.middle_ne_top
    exact top_unique (by simpa only [htop] using hNle)

/-- Every ambient minimal normal subgroup is the checked middle state. -/
theorem minimalNormal_eq_middle
    (N : Subgroup G) (hN : IsMinimalNormalSubgroup N) :
    N = D.middle := by
  rcases D.normal_eq_bot_or_middle_or_top N hN.1 with hbot | hmiddle | htop
  · exact (hN.2.1 hbot).elim
  · exact hmiddle
  · exfalso
    apply D.middle_ne_top
    have hle : D.middle ≤ N := by
      rw [htop]
      exact le_top
    exact (hN.2.2 D.middle inferInstance D.middle_ne_bot hle).trans htop

/-- In a three-state normal chain, the socle is exactly the middle state. -/
theorem finiteGroupSocle_eq_middle :
    finiteGroupSocle G = D.middle := by
  apply le_antisymm
  · rw [finiteGroupSocle]
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨N, hN, hx⟩
    rw [D.minimalNormal_eq_middle N hN] at hx
    exact hx
  · intro x hx
    exact Subgroup.subset_normalClosure
      ⟨D.middle, D.middle_isMinimalNormalSubgroup, hx⟩

include D
/-- The literal middle-state generator is a one-position socle witness for
the ambient group. -/
theorem socleNormalGeneratorBound : SocleNormalGeneratorBound G 1 := by
  refine ⟨fun _ ↦ D.generator, ?_⟩
  calc
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ D.generator)) =
        D.middle := normalClosure_generator_eq_middle (D := D)
    _ = finiteGroupSocle G := (finiteGroupSocle_eq_middle (D := D)).symm

/-- Transport all three checked normal states and the distinguished literal
generator across a group equivalence. -/
noncomputable def mapEquiv (e : G ≃* H) :
    FiniteThreeNormalChainData H where
  middle := D.middle.map e.toMonoidHom
  middle_normal := D.middle_normal.map e.toMonoidHom e.surjective
  middle_ne_bot := by
    intro h
    apply D.middle_ne_bot
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using h
  middle_ne_top := by
    intro h
    apply D.middle_ne_top
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      using h
  normal_eq_bot_or_middle_or_top := by
    intro N hN
    have hcomap : (N.comap e.toMonoidHom).Normal :=
      hN.comap e.toMonoidHom
    rcases D.normal_eq_bot_or_middle_or_top
        (N.comap e.toMonoidHom) hcomap with hbot | hmiddle | htop
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective
          (f := e.toMonoidHom) e.surjective N,
        hbot, Subgroup.map_bot]
    · right; left
      rw [← Subgroup.map_comap_eq_self_of_surjective
          (f := e.toMonoidHom) e.surjective N,
        hmiddle]
    · right; right
      rw [← Subgroup.map_comap_eq_self_of_surjective
          (f := e.toMonoidHom) e.surjective N,
        htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  generator := e D.generator
  generator_mem := ⟨D.generator, D.generator_mem, rfl⟩
  generator_ne_one := by
    intro h
    apply D.generator_ne_one
    apply e.injective
    simpa only [map_one] using h

/-- The middle quotient has no proper nontrivial normal subgroup.  This is
derived from the checked registry by the quotient correspondence theorem. -/
@[implicit_reducible] noncomputable def quotientMiddleIsSimpleGroup :
    IsSimpleGroup (G ⧸ D.middle) where
  toNontrivial := not_subsingleton_iff_nontrivial.mp (by
    intro h
    exact D.middle_ne_top
      (QuotientGroup.subgroup_eq_top_of_subsingleton D.middle h))
  eq_bot_or_eq_top_of_normal N hN := by
    letI : N.Normal := hN
    have hcomap : (N.comap (QuotientGroup.mk' D.middle)).Normal :=
      hN.comap (QuotientGroup.mk' D.middle)
    have hmiddle : D.middle ≤ N.comap (QuotientGroup.mk' D.middle) :=
      QuotientGroup.le_comap_mk' D.middle N
    rcases D.normal_eq_bot_or_middle_or_top
        (N.comap (QuotientGroup.mk' D.middle)) hcomap with
        hbot | heq | htop
    · exfalso
      apply D.middle_ne_bot
      exact bot_unique (by simpa only [hbot] using hmiddle)
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective D.middle) N,
        heq, QuotientGroup.map_mk'_self]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective D.middle) N,
        htop, Subgroup.map_top_of_surjective
          (QuotientGroup.mk' D.middle)
          (QuotientGroup.mk'_surjective D.middle)]

/-- The bottom quotient inherits the three-state chain and its literal
middle generator. -/
noncomputable def bottomQuotientSocleGenerator :
    SocleNormalGeneratorBound (G ⧸ (⊥ : Subgroup G)) 1 :=
  FiniteThreeNormalChainData.socleNormalGeneratorBound
    (D := mapEquiv (D := D) QuotientGroup.quotientBot.symm)

/-- The middle quotient is simple, so one nonidentity element normally
generates its socle. -/
noncomputable def middleQuotientSocleGenerator :
    SocleNormalGeneratorBound (G ⧸ D.middle) 1 := by
  letI : IsSimpleGroup (G ⧸ D.middle) :=
    quotientMiddleIsSimpleGroup (D := D)
  exact socleNormalGeneratorBound_one_of_isSimpleGroup _

/-- The top quotient is trivial and admits the padded identity witness. -/
noncomputable def topQuotientSocleGenerator :
    SocleNormalGeneratorBound (G ⧸ (⊤ : Subgroup G)) 1 := by
  letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
    QuotientGroup.subsingleton_quotient_top
  exact socleNormalGeneratorBound_one_of_subsingleton _

/-- A three-state normal chain gives a uniformly padded two-position socle
generator on every quotient.  This packages the bottom/middle/top dispatch
once, so named structural families do not need a finite quotient table. -/
noncomputable def quotientSocleGeneratorBound_two
    (N : {N : Subgroup G // N.Normal}) :
    SocleNormalGeneratorBound (G ⧸ N.1) 2 := by
  rcases D.normal_eq_bot_or_middle_or_top N.1 N.2 with
      hbot | hmiddle | htop
  · let e : G ⧸ N.1 ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans
        QuotientGroup.quotientBot
    exact ((D.mapEquiv e.symm).socleNormalGeneratorBound).mono
      (by norm_num)
  · letI : IsSimpleGroup (G ⧸ D.middle) :=
      D.quotientMiddleIsSimpleGroup
    let e : G ⧸ N.1 ≃* G ⧸ D.middle :=
      QuotientGroup.quotientMulEquivOfEq hmiddle
    letI : IsSimpleGroup (G ⧸ N.1) := e.isSimpleGroup
    exact (socleNormalGeneratorBound_one_of_isSimpleGroup _).mono
      (by norm_num)
  · letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
      QuotientGroup.subsingleton_quotient_top
    letI : Subsingleton (G ⧸ N.1) :=
      (QuotientGroup.quotientMulEquivOfEq htop).toEquiv.subsingleton
    exact (socleNormalGeneratorBound_one_of_subsingleton _).mono
      (by norm_num)

end FiniteThreeNormalChainData
end SymmetricSubgroupAsymptotics

end
