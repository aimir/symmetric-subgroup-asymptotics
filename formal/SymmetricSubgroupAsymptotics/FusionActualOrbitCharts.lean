import SymmetricSubgroupAsymptotics.FusionPhysicalCharts
import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Exact physical charts from actual original orbits

An orbit and its entire complement partition the original finite points.
Their finite labellings give a physical chart, and the two original
restriction actions reconstruct the original permutation literally. The
first chart projection is therefore the conjugate of the actual orbit
image, with its order and group properties transported by an equivalence.
No binary hypothesis on the entire subgroup or its complement is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

variable {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)

/-- The existing actual invariant orbit, with its original H-action. -/
abbrev orbitSet : SubMulAction H (Fin n) :=
  PermutationCharacterRankSplit.orbitSubset (G := H) x

/-- The faithful permutation image on the actual original orbit type. -/
abbrev orbitImage : Subgroup (Equiv.Perm (orbitSet H x)) :=
  PermutationCharacterRankSplit.Image (orbitSet H x)

variable (hw : Nat.card (MulAction.orbit H x) = w)

include hw in
theorem degree_le : w ≤ n := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : MulAction.orbit H x → Fin n) Subtype.val_injective
  simpa only [hw, Nat.card_fin] using h

include hw in
theorem complement_card : Nat.card ↥((orbitSet H x)ᶜ) = n-w := by
  have h := PermutationCharacterRankSplit.card_split (orbitSet H x)
  change Nat.card (MulAction.orbit H x) + Nat.card ↥((orbitSet H x)ᶜ) = Nat.card (Fin n) at h
  rw [hw, Nat.card_fin] at h
  omega

def orbitEquiv : Fin w ≃ orbitSet H x :=
  (Finite.equivFinOfCardEq (show Nat.card (orbitSet H x) = w from hw)).symm

def complementEquiv : Fin (n-w) ≃ ↥((orbitSet H x)ᶜ) :=
  (Finite.equivFinOfCardEq (complement_card H x hw)).symm

/-- The existing finite-set partition gives the whole original chart. -/
def chart : Fin w ⊕ Fin (n-w) ≃ Fin n :=
  (Equiv.sumCongr (orbitEquiv H x hw) (complementEquiv H x hw)).trans
    (Equiv.Set.sumCompl (orbitSet H x : Set (Fin n)))

theorem chart_inl (i : Fin w) :
    chart H x hw (Sum.inl i) = (orbitEquiv H x hw i : Fin n) := rfl

theorem chart_inr (i : Fin (n-w)) :
    chart H x hw (Sum.inr i) = (complementEquiv H x hw i : Fin n) := rfl

/-- The first chart block is exactly the selected original orbit. -/
theorem chart_first_range :
    Set.range (fun i : Fin w => chart H x hw (Sum.inl i)) = MulAction.orbit H x := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact (orbitEquiv H x hw i).property
  · intro hy
    refine ⟨(orbitEquiv H x hw).symm ⟨y,hy⟩, ?_⟩
    change chart H x hw (Sum.inl ((orbitEquiv H x hw).symm ⟨y,hy⟩)) = y
    rw [chart_inl, Equiv.apply_symm_apply]

def firstHom : H →* Equiv.Perm (Fin w) :=
  (orbitEquiv H x hw).symm.permCongrHom.toMonoidHom.comp
    (PermutationCharacterRankSplit.restrictionHom (orbitSet H x))

def secondHom : H →* Equiv.Perm (Fin (n-w)) :=
  (complementEquiv H x hw).symm.permCongrHom.toMonoidHom.comp
    (PermutationCharacterRankSplit.restrictionHom ((orbitSet H x)ᶜ))

def pairHom : H →* Equiv.Perm (Fin w) × Equiv.Perm (Fin (n-w)) :=
  (firstHom H x hw).prod (secondHom H x hw)

/-- Both coordinates are restrictions of the same original element. -/
theorem chart_pairHom_apply (g : H) (z : Fin w ⊕ Fin (n-w)) :
    chart H x hw (Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw g) z) =
      (g : Equiv.Perm (Fin n)) (chart H x hw z) := by
  rcases z with i | i
  · change chart H x hw (Sum.inl (firstHom H x hw g i)) =
      (g : Equiv.Perm (Fin n)) (chart H x hw (Sum.inl i))
    rw [chart_inl, chart_inl]
    change ((orbitEquiv H x hw)
      ((orbitEquiv H x hw).symm (g • orbitEquiv H x hw i)) : Fin n) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · change chart H x hw (Sum.inr (secondHom H x hw g i)) =
      (g : Equiv.Perm (Fin n)) (chart H x hw (Sum.inr i))
    rw [chart_inr, chart_inr]
    change ((complementEquiv H x hw)
      ((complementEquiv H x hw).symm (g • complementEquiv H x hw i)) : Fin n) = _
    rw [Equiv.apply_symm_apply]
    rfl

theorem chart_conjugate_pair (g : H) :
    (chart H x hw).symm.permCongr (g : Equiv.Perm (Fin n)) =
      Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw g) := by
  apply Equiv.ext
  intro z
  apply (chart H x hw).injective
  change chart H x hw ((chart H x hw).symm
    ((g : Equiv.Perm (Fin n)) (chart H x hw z))) = _
  rw [Equiv.apply_symm_apply]
  exact (chart_pairHom_apply H x hw g z).symm

/-- Every original element preserves the first block in the new chart. -/
theorem chart_preserves :
    ∀ k ∈ relabelSubgroup (chart H x hw).symm H,
      Set.MapsTo k (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))
        (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w))) := by
  intro k hk
  change k ∈ H.map (chart H x hw).symm.permCongrHom.toMonoidHom at hk
  obtain ⟨g,hg,rfl⟩ := hk
  rw [show (chart H x hw).symm.permCongrHom.toMonoidHom g =
      Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw ⟨g,hg⟩)
    from chart_conjugate_pair H x hw ⟨g,hg⟩]
  rintro _ ⟨i,rfl⟩
  exact ⟨firstHom H x hw ⟨g,hg⟩ i,rfl⟩

/-- The pullback is the image of the same original H under its two
restrictions, so no independence between orbit and complement is imposed. -/
theorem blockPullback_eq_range :
    fusionPhysicalBlockPullback (relabelSubgroup (chart H x hw).symm H) =
      (pairHom H x hw).range := by
  ext p
  constructor
  · intro hp
    change Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) p ∈
      H.map (chart H x hw).symm.permCongrHom.toMonoidHom at hp
    obtain ⟨g,hg,he⟩ := hp
    refine ⟨⟨g,hg⟩,?_⟩
    apply Equiv.Perm.sumCongrHom_injective
    exact (chart_conjugate_pair H x hw ⟨g,hg⟩).symm.trans he
  · rintro ⟨g,rfl⟩
    change Equiv.Perm.sumCongrHom (Fin w) (Fin (n-w)) (pairHom H x hw g) ∈
      H.map (chart H x hw).symm.permCongrHom.toMonoidHom
    exact ⟨g,g.property,chart_conjugate_pair H x hw g⟩

/-- The literal first projection used by the physical fusion interfaces. -/
def chartAction : Subgroup (Equiv.Perm (Fin w)) :=
  (fusionPhysicalBlockPullback (relabelSubgroup (chart H x hw).symm H)).map
    (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w))))

theorem chartAction_eq_range : chartAction H x hw = (firstHom H x hw).range := by
  rw [chartAction, blockPullback_eq_range, MonoidHom.map_range]
  congr 1

theorem chartAction_eq_map :
    chartAction H x hw = (orbitImage H x).map
      (orbitEquiv H x hw).symm.permCongrHom.toMonoidHom := by
  rw [chartAction_eq_range, firstHom, MonoidHom.range_comp]

/-- The original orbit image, not the whole H, is identified with the
literal first physical projection. This retains the actual image order. -/
def imageEquiv : orbitImage H x ≃* chartAction H x hw :=
  ((orbitImage H x).equivMapOfInjective
    (orbitEquiv H x hw).symm.permCongrHom.toMonoidHom
    (orbitEquiv H x hw).symm.permCongrHom.injective).trans
      (MulEquiv.subgroupCongr (chartAction_eq_map H x hw).symm)

theorem chartAction_card : Nat.card (chartAction H x hw) = Nat.card (orbitImage H x) :=
  (Nat.card_congr (imageEquiv H x hw).toEquiv).symm

theorem chartAction_isPGroup (p : ℕ) (hP : IsPGroup p (orbitImage H x)) :
    IsPGroup p (chartAction H x hw) := hP.of_equiv (imageEquiv H x hw)

/-- Transitivity comes from the actual orbit and the same restriction map. -/
theorem chartAction_transitive : MulAction.IsPretransitive (chartAction H x hw) (Fin w) := by
  rw [chartAction_eq_range]
  constructor
  intro a b
  have ha : (orbitEquiv H x hw a : Fin n) ∈ MulAction.orbit H x :=
    (orbitEquiv H x hw a).property
  have hb : (orbitEquiv H x hw b : Fin n) ∈ MulAction.orbit H x :=
    (orbitEquiv H x hw b).property
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ha
  obtain ⟨j,hj⟩ := MulAction.mem_orbit_iff.mp hb
  have ht : (j*g⁻¹) • orbitEquiv H x hw a = orbitEquiv H x hw b := by
    apply Subtype.ext
    change (j*g⁻¹) • (orbitEquiv H x hw a : Fin n) = (orbitEquiv H x hw b : Fin n)
    rw [← hg, ← hj]
    simp only [mul_smul, inv_smul_smul]
  refine ⟨⟨firstHom H x hw (j*g⁻¹),⟨j*g⁻¹,rfl⟩⟩,?_⟩
  change (orbitEquiv H x hw).symm ((j*g⁻¹) • orbitEquiv H x hw a) = b
  rw [ht, Equiv.symm_apply_apply]

include hw in
/-- Ready-to-use chart existence from structural properties of the
actual orbit image. The rest of the original subgroup is unrestricted. -/
theorem exists_chart_of_image_bounds (p cap : ℕ)
    (hP : IsPGroup p (orbitImage H x)) (hcard : Nat.card (orbitImage H x) ≤ cap) :
    ∃ e : Fin w ⊕ Fin (n-w) ≃ Fin n,
      Set.range (fun i : Fin w => e (Sum.inl i)) = MulAction.orbit H x ∧
      (∀ k ∈ relabelSubgroup e.symm H,
        Set.MapsTo k (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))
          (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))) ∧
      IsPGroup p ((fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
        (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w))))) ∧
      MulAction.IsPretransitive
        ((fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
          (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w))))) (Fin w) ∧
      Nat.card ((fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
        (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w))))) ≤ cap := by
  refine ⟨chart H x hw, chart_first_range H x hw, chart_preserves H x hw,
    chartAction_isPGroup H x hw p hP, chartAction_transitive H x hw, ?_⟩
  change Nat.card (chartAction H x hw) ≤ cap
  rw [chartAction_card]
  exact hcard

end SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

end
