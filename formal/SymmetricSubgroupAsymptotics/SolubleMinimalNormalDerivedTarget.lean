import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import SymmetricSubgroupAsymptotics.ElementaryChartIrreducibleStructure

/-!
# Cyclic-dual targets from a soluble quotient and an elementary minimal normal subgroup

This is the extension-theoretic part of the primitive-affine argument with
primitivity removed from its statement.  A nontrivial elementary normal
subgroup which is minimal and self-centralizing, with nontrivial soluble
quotient, is a derived cyclic target.  The proof uses the literal quotient
map and does not require the extension to split.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative commutatorElement

namespace SymmetricSubgroupAsymptotics

namespace ElementaryMinimalNormalChart

variable {G : Type} [Group G] [Finite G]
  {E : Subgroup G} [E.Normal]
  (C : ElementaryMinimalNormalChart E)

/-- Dimension of the literal elementary chart. -/
def dimension : ℕ := Module.finrank (ZMod C.p) C.V

omit [Finite G] [E.Normal] in
theorem dimension_pos [Nontrivial C.V] : 0 < C.dimension :=
  Module.finrank_pos_iff.mpr inferInstance

/-- A concrete nontrivial coordinate character of the elementary subgroup. -/
noncomputable def coordinateCharacter [Nontrivial C.V] :
    E →* Multiplicative (ZMod C.p) := by
  let b := Module.finBasis (ZMod C.p) C.V
  exact
    { toFun := fun e ↦ Multiplicative.ofAdd
        (b.equivFun (C.equiv e).toAdd ⟨0, C.dimension_pos⟩)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }

omit [Finite G] [E.Normal] in
theorem coordinateCharacter_ne_one [Nontrivial C.V] :
    C.coordinateCharacter ≠ 1 := by
  let b := Module.finBasis (ZMod C.p) C.V
  let z : Fin C.dimension → ZMod C.p :=
    Pi.single ⟨0, C.dimension_pos⟩ 1
  let e : E := C.equiv.symm
    (Multiplicative.ofAdd (b.equivFun.symm z))
  intro h
  have he := DFunLike.congr_fun h e
  change Multiplicative.ofAdd
      (b.equivFun (C.equiv e).toAdd ⟨0, C.dimension_pos⟩) = 1 at he
  have hz : z ⟨0, C.dimension_pos⟩ = 1 := Pi.single_eq_same _ _
  have hezero :
      b.equivFun (C.equiv e).toAdd ⟨0, C.dimension_pos⟩ = 0 :=
    ofAdd_eq_one.mp he
  have heone :
      b.equivFun (C.equiv e).toAdd ⟨0, C.dimension_pos⟩ = 1 := by
    have hev : (C.equiv e).toAdd = b.equivFun.symm z := by
      simp only [e, C.equiv.apply_symm_apply, toAdd_ofAdd]
    rw [hev]
    exact (congrFun (b.equivFun.apply_symm_apply z)
      ⟨0, C.dimension_pos⟩).trans hz
  have h10 : (1 : ZMod C.p) = 0 := heone.symm.trans hezero
  exact one_ne_zero h10

end ElementaryMinimalNormalChart

namespace SolubleMinimalNormalExtension

variable {G : Type} [Group G] [Finite G]
  {E : Subgroup G} [E.Normal]

omit [Finite G] in
/-- A nonidentity quotient element lifted inside a subgroup forces a
nontrivial mixed commutator with a self-centralizing kernel. -/
theorem comm_ne_bot_of_quotient_projection
    (hself : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (H : Subgroup G) (r : G ⧸ E) (hr : r ≠ 1)
    (hH : ∃ y ∈ H, QuotientGroup.mk' E y = r) :
    ⁅H, E⁆ ≠ ⊥ := by
  obtain ⟨y, hyH, hyr⟩ := hH
  intro hbot
  have hcomm : ∀ e ∈ E, y * e = e * y := by
    intro e he
    have hm : ⁅y, e⁆ ∈ ⁅H, E⁆ :=
      Subgroup.commutator_mem_commutator hyH he
    rw [hbot] at hm
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hm)
  have hyE := hself y hcomm
  have hyone : QuotientGroup.mk' E y = 1 :=
    (QuotientGroup.eq_one_iff y).mpr hyE
  exact hr (hyr.symm.trans hyone)

omit [Finite G] in
/-- The derived term immediately below the first vanishing quotient term is
the whole elementary kernel. -/
theorem derived_eq_kernel
    (hmin : ∀ W : Subgroup G, W.Normal → W ≤ E → W = ⊥ ∨ W = E)
    (hself : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (D : SolubleDerivedLength (G ⧸ E)) :
    derivedSeries G (D.t + 1) = E := by
  let π := QuotientGroup.mk' E
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective E
  apply le_antisymm
  · intro y hy
    have hm := map_derivedSeries_le_derivedSeries π (D.t + 1) ⟨y, hy, rfl⟩
    rw [D.top_eq] at hm
    exact (QuotientGroup.eq_one_iff y).mp (Subgroup.mem_bot.mp hm)
  · have hcomm : ∀ k, k ≤ D.t → ⁅derivedSeries G k, E⁆ ≠ ⊥ := by
      intro k hk
      obtain ⟨r, hrt, hr⟩ := SolubleDerivedLength.exists_ne_one D
      have hrk : r ∈ derivedSeries (G ⧸ E) k :=
        derivedSeries_antitone _ hk hrt
      rw [← map_derivedSeries_eq hsurj k] at hrk
      obtain ⟨y, hy, hyr⟩ := hrk
      exact comm_ne_bot_of_quotient_projection hself
        (derivedSeries G k) r hr ⟨y, hy, hyr⟩
    have hk : ∀ k, k ≤ D.t + 1 → E ≤ derivedSeries G k := by
      intro k
      induction k with
      | zero =>
          intro _
          rw [derivedSeries_zero]
          exact le_top
      | succ k ih =>
          intro hkt
          have hprev := ih (by omega)
          have hne := hcomm k (by omega)
          have hnormal : (⁅derivedSeries G k, E⁆).Normal :=
            Subgroup.commutator_normal _ _
          rcases hmin _ hnormal (Subgroup.commutator_le_right _ _) with h | h
          · exact absurd h hne
          · rw [← h, derivedSeries_succ]
            exact Subgroup.commutator_mono le_rfl hprev
    exact hk (D.t + 1) le_rfl

/-- The nonsplit soluble extension is a cyclic-dual target over the prime
of its elementary kernel. -/
noncomputable def derivedCyclicTarget
    (C : ElementaryMinimalNormalChart E) [Nontrivial C.V]
    (hmin : ∀ W : Subgroup G, W.Normal → W ≤ E → W = ⊥ ∨ W = E)
    (hself : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (D : SolubleDerivedLength (G ⧸ E)) :
    DerivedHead.DerivedCyclicTarget G E D.t C.p where
  derived_eq := derived_eq_kernel hmin hself D
  character := C.coordinateCharacter
  self_centralizing := hself
  absorbing := by
    intro W hW hWE
    rcases hmin W hW hWE with h | h
    · rw [h]
      exact bot_le
    · obtain ⟨r, hrt, hr⟩ := SolubleDerivedLength.exists_ne_one D
      have hrmap : r ∈ (derivedSeries G D.t).map (QuotientGroup.mk' E) := by
        rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective E) D.t]
        exact hrt
      obtain ⟨y, hy, hyr⟩ := hrmap
      have hne := comm_ne_bot_of_quotient_projection hself
        (derivedSeries G D.t) r hr ⟨y, hy, hyr⟩
      have hnormal : (⁅derivedSeries G D.t, E⁆).Normal :=
        Subgroup.commutator_normal _ _
      rcases hmin _ hnormal (Subgroup.commutator_le_right _ _) with h' | h'
      · exact absurd h' hne
      · rw [h]
        exact h'.symm.le
  separating := DerivedHead.separating_of_minimal hmin _
    C.coordinateCharacter_ne_one

end SolubleMinimalNormalExtension
end SymmetricSubgroupAsymptotics

end
