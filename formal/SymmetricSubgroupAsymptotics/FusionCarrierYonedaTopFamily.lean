import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaIncidence
import SymmetricSubgroupAsymptotics.FusionCarrierWeightedIncidence

/-!
# Finite families of Yoneda tops on one reversible carrier

An unowned residual axis need not have one top fixed in advance.  This file
allows a finite family of possible tops and lets each accepted epimorphism
select its own member.  The retained flag is the dependent pair consisting of
that selected top and its literal tower flag.  Consequently the weighted-cell
cost is

`\sum_s |Flag_s| * YonedaBound_s`,

which is bounded by the sum of the individual tower capacities.  No number of
tops is multiplied by a worst-case capacity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite
open Non2UnipotentPrefixFiniteMenu

/-- A finite menu of abelian Yoneda towers from the same carrier quotient to
possibly different quotient tops of one comparator group. -/
structure AxisYonedaTopFamily
    {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {N : {N : Subgroup U // N.Normal}}
    (K : FusionAxisCarrier U N) (R : Type) [Group R] where
  Index : Type
  [index_finite : Finite Index]
  tower : Index → AxisYonedaTower K R

attribute [instance] AxisYonedaTopFamily.index_finite

namespace AxisYonedaTopFamily

variable {w b : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  {N : {N : Subgroup U // N.Normal}}
  (K : FusionAxisCarrier U N)
  (R : Type) [Group R] [Finite R]
  (F : AxisYonedaTopFamily K R)

/-- The retained flag remembers which top was selected and then the complete
literal restriction flag belonging to that top's tower. -/
def Flag (J : Subgroup (Equiv.Perm (Fin b))) : Type :=
  Σ s : F.Index, (F.tower s).tower.Flag J

instance flag_finite (J : Subgroup (Equiv.Perm (Fin b))) :
    Finite (F.Flag K R J) := by
  unfold Flag
  infer_instance

/-- The transparent dependent-sum presentation of the retained family flag. -/
def flagEquiv (J : Subgroup (Equiv.Perm (Fin b))) :
    F.Flag K R J ≃ (Σ s : F.Index, (F.tower s).tower.Flag J) :=
  Equiv.refl _

/-- The complete quotient map and retained flag selected by an accepted
epimorphism.  The selector is allowed to inspect the full accepted state. -/
def cell
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (select : FusionCarrierAcceptedEpi K.checked J Accepted → F.Index)
    (γ : FusionCarrierAcceptedEpi K.checked J Accepted) :
    CompleteQuotientMap J R × F.Flag K R J :=
  let T := F.tower (select γ)
  (fusionCarrierTopQuotientMap T.M T.top T.tower.top_surjective γ.1,
    ⟨select γ, T.tower.flag J γ.1.1⟩)

/-- The fibre cost attached to a retained top/flag pair. -/
def fibreCost
    (J : Subgroup (Equiv.Perm (Fin b))) (a : F.Flag K R J) : ℕ :=
  (F.tower a.1).tower.bound

omit [Finite R] in
/-- Fixing the complete quotient map and the selected top/flag pair leaves at
most the Yoneda fibre of that selected tower. -/
theorem cell_fibre_card_le
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (select : FusionCarrierAcceptedEpi K.checked J Accepted → F.Index)
    (d : CompleteQuotientMap J R) (a : F.Flag K R J) :
    Nat.card {γ : FusionCarrierAcceptedEpi K.checked J Accepted //
      F.cell K R J Accepted select γ = (d, a)} ≤ F.fibreCost K R J a := by
  obtain ⟨s, a⟩ := a
  let fixedCell : FusionCarrierAcceptedEpi K.checked J Accepted →
      CompleteQuotientMap J R × F.Flag K R J := fun γ =>
    (fusionCarrierTopQuotientMap (F.tower s).M (F.tower s).top
        (F.tower s).tower.top_surjective γ.1,
      ⟨s, (F.tower s).tower.flag J γ.1.1⟩)
  let Y := {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
    fixedCell δ = (d, ⟨s, a⟩)}
  calc
    Nat.card {γ : FusionCarrierAcceptedEpi K.checked J Accepted //
        F.cell K R J Accepted select γ = (d, ⟨s, a⟩)} ≤ Nat.card Y :=
      Nat.card_le_card_of_injective (fun γ => (⟨γ.1, by
        have hflag := congrArg Prod.snd γ.2
        have hs : select γ.1 = s := (Sigma.mk.inj_iff.mp hflag).1
        let g : F.Index → CompleteQuotientMap J R × F.Flag K R J := fun t =>
          (fusionCarrierTopQuotientMap (F.tower t).M (F.tower t).top
              (F.tower t).tower.top_surjective γ.1.1,
            ⟨t, (F.tower t).tower.flag J γ.1.1.1⟩)
        have hg : g (select γ.1) = g s := congrArg g hs
        have hc : g (select γ.1) = (d, ⟨s, a⟩) := by
          simpa only [g, cell] using γ.2
        exact hg.symm.trans hc⟩ : Y)) (by
          intro γ δ hγδ
          apply Subtype.ext
          exact congrArg (fun z : Y ↦ z.1) hγδ)
    _ ≤ Nat.card {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
        axisYonedaCell K (some (F.tower s)) J Accepted δ = (d, a)} :=
      Nat.card_le_card_of_injective (fun δ => (⟨δ.1, by
        have htop := congrArg Prod.fst δ.2
        have hflag := congrArg Prod.snd δ.2
        change (fusionCarrierTopQuotientMap (F.tower s).M (F.tower s).top
            (F.tower s).tower.top_surjective δ.1.1,
          (F.tower s).tower.flag J δ.1.1.1) = (d, a)
        apply Prod.ext
        · exact htop
        · exact eq_of_heq (Sigma.mk.inj_iff.mp hflag).2⟩ :
          {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
            axisYonedaCell K (some (F.tower s)) J Accepted δ = (d, a)})) (by
          intro γ δ hγδ
          apply Subtype.ext
          exact congrArg (fun z : {δ : FusionCarrierAcceptedEpi
            K.checked J Accepted //
              axisYonedaCell K (some (F.tower s)) J Accepted δ = (d, a)} ↦
                z.1) hγδ)
    _ ≤ (F.tower s).tower.bound :=
      axisYonedaCell_fibre_card_le K (some (F.tower s)) J Accepted (d, a)

omit [Finite R] in
/-- The exact weighted-cell sum factors over the selected tops. -/
theorem sum_fibreCost_eq
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ a : F.Flag K R J, F.fibreCost K R J a) =
      ∑ s : F.Index,
        Fintype.card ((F.tower s).tower.Flag J) * (F.tower s).tower.bound := by
  calc
    (∑ a : F.Flag K R J, F.fibreCost K R J a) =
        ∑ a : (Σ s : F.Index, (F.tower s).tower.Flag J),
          (F.tower a.1).tower.bound :=
      Fintype.sum_equiv (F.flagEquiv K R J) _ _ (fun _ ↦ rfl)
    _ =
        ∑ s : F.Index, ∑ _a : (F.tower s).tower.Flag J,
          (F.tower s).tower.bound := Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id]

omit [Finite R] in
/-- The whole varying-top cost is bounded by the sum of the individual
annihilator-aware Yoneda capacities. -/
theorem sum_fibreCost_le_capacity
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ a : F.Flag K R J, F.fibreCost K R J a) ≤
      ∑ s : F.Index, (F.tower s).tower.capacity J := by
  rw [F.sum_fibreCost_eq K R J]
  exact Finset.sum_le_sum (fun s _ ↦ by
    simpa only [Nat.card_eq_fintype_card] using
      (F.tower s).tower.card_flag_mul_bound_le_capacity J)

/-- Incidence for a finite family of epimorphism-selected tops.  The family is
paid by the sum of its tower capacities, rather than its cardinality times a
worst-case tower. -/
theorem acceptedEpi_card_le
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (select : FusionCarrierAcceptedEpi K.checked J Accepted → F.Index) :
    (Nat.card (FusionCarrierAcceptedEpi K.checked J Accepted) : ℝ) ≤
      ((∑ s : F.Index, (F.tower s).tower.capacity J : ℕ) : ℝ) *
        completeQuotientWeight (R := R) J := by
  have hcells := fusionCarrierAcceptedEpi_card_le_of_weightedRetainedCells
    K.checked J Accepted (F.cell K R J Accepted select) (F.fibreCost K R J)
      (F.cell_fibre_card_le K R J Accepted select)
  exact hcells.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (F.sum_fibreCost_le_capacity K R J))
    (completeQuotientWeight_nonneg (R := R) J))

/-- Numerical owner-capacity form of the varying-top incidence theorem. -/
theorem acceptedEpi_card_le_ownerCapacity
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (select : FusionCarrierAcceptedEpi K.checked J Accepted → F.Index)
    (D eta : ℝ)
    (hcapacity :
      ((∑ s : F.Index, (F.tower s).tower.capacity J : ℕ) : ℝ) ≤
        D * (2 : ℝ) ^ (eta * b)) :
    (Nat.card (FusionCarrierAcceptedEpi K.checked J Accepted) : ℝ) ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  exact (F.acceptedEpi_card_le K R J Accepted select).trans
    (mul_le_mul_of_nonneg_right hcapacity
      (completeQuotientWeight_nonneg (R := R) J))

end AxisYonedaTopFamily

end SymmetricSubgroupAsymptotics

end
