import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# One socle normal generator from a two-point normal lattice

Finite catalogue rows often prove that every normal subgroup is either
bottom or top.  This file converts that checked normal-lattice statement to
the one-position socle input used by Zmud's theorem.  It also records the
trivial-group endpoint, which occurs for the quotient by the top normal
state.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A nontrivial group with no proper nontrivial normal subgroup has full
socle.  The proof uses the literal top subgroup as a minimal normal subgroup;
it does not identify the group with any named simple group. -/
theorem finiteGroupSocle_eq_top_of_normal_eq_bot_or_top
    (G : Type) [Group G] [Nontrivial G]
    (hnormal : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) :
    finiteGroupSocle G = ⊤ := by
  have htop : IsMinimalNormalSubgroup (⊤ : Subgroup G) := by
    refine ⟨inferInstance, top_ne_bot, ?_⟩
    intro N hN hNne _
    exact (hnormal N hN).resolve_left hNne
  apply top_unique
  intro x _
  exact Subgroup.subset_normalClosure ⟨⊤, htop, Subgroup.mem_top x⟩

/-- A specified nonidentity element normally generates the socle when the
normal lattice consists only of bottom and top. -/
theorem socleNormalGeneratorBound_one_of_normal_eq_bot_or_top
    {G : Type} [Group G] [Nontrivial G]
    (x : G) (hx : x ≠ 1)
    (hnormal : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) :
    SocleNormalGeneratorBound G 1 := by
  let generators : Fin 1 → G := fun _ ↦ x
  refine ⟨generators, ?_⟩
  have hclosure : Subgroup.normalClosure (Set.range generators) = ⊤ := by
    exact (hnormal _ inferInstance).resolve_left (by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.subset_normalClosure
          (Set.mem_range_self (0 : Fin 1))
      exact hx (Subgroup.mem_bot.mp hxbot))
  exact hclosure.trans
    (finiteGroupSocle_eq_top_of_normal_eq_bot_or_top G hnormal).symm

/-- Instance-oriented form used after a finite registry has installed an
`IsSimpleGroup` instance. -/
theorem socleNormalGeneratorBound_one_of_isSimpleGroup
    (G : Type) [Group G] [IsSimpleGroup G] :
    SocleNormalGeneratorBound G 1 := by
  let x : G := Classical.choose (exists_ne (1 : G))
  have hx : x ≠ 1 := Classical.choose_spec (exists_ne (1 : G))
  exact socleNormalGeneratorBound_one_of_normal_eq_bot_or_top x hx
    (fun N hN ↦ hN.eq_bot_or_eq_top)

/-- A trivial group also has the padded one-position socle witness. -/
theorem socleNormalGeneratorBound_one_of_subsingleton
    (G : Type) [Group G] [Subsingleton G] :
    SocleNormalGeneratorBound G 1 := by
  letI : Subsingleton (Subgroup G) :=
    Subgroup.subsingleton_iff.mpr inferInstance
  exact ⟨fun _ ↦ 1, Subsingleton.elim _ _⟩

end SymmetricSubgroupAsymptotics

end
