import SymmetricSubgroupAsymptotics.C1ActualGraphs
import SymmetricSubgroupAsymptotics.FusionOrbitPointing
import Mathlib.GroupTheory.IndexNormal

/-! # First c=1 original-action application
A literal regular C3 action has its original normalizer of order six.
The physical fusion interface retains the entire surviving character sum.
Naturality refers to the actual accepted family under coordinate relabelling;
it does not assume any numerical capacity bound.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

def ternaryRegularRepresentation : TernaryCyclic →* Equiv.Perm TernaryCyclic :=
  MulAction.toPermHom TernaryCyclic TernaryCyclic

def ternaryRegularAction : Subgroup (Equiv.Perm TernaryCyclic) :=
  ternaryRegularRepresentation.range

def ternaryRegularEquiv : TernaryCyclic ≃* ternaryRegularAction :=
  MonoidHom.ofInjective (f := ternaryRegularRepresentation) MulAction.toPerm_injective

theorem ternaryRegularAction_card : Nat.card ternaryRegularAction = 3 := by
  rw [← Nat.card_congr ternaryRegularEquiv.toEquiv]
  simp [TernaryCyclic,Nat.card_eq_fintype_card]

instance ternaryRegularAction_normal : ternaryRegularAction.Normal := by
  apply Subgroup.normal_of_index_eq_two
  have h := ternaryRegularAction.card_mul_index
  rw [ternaryRegularAction_card] at h
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,TernaryCyclic] at h
  omega

theorem ternaryRegularAction_normalizer_card :
    Nat.card (Subgroup.normalizer (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) = 6 := by
  rw [Subgroup.normalizer_eq_top]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,TernaryCyclic]

theorem ternaryRegularAction_transitive (x y : TernaryCyclic) :
    ∃ g : ternaryRegularAction, (g : Equiv.Perm TernaryCyclic) x = y := by
  refine ⟨ternaryRegularEquiv (y*x⁻¹),?_⟩
  change (y*x⁻¹)*x=y
  exact inv_mul_cancel_right _ _

variable {Z : Type*}

def ternaryPhysicalCoordinateEquiv :
    (TernaryCyclic × Equiv.Perm Z) ≃* (ternaryRegularAction × Equiv.Perm Z) :=
  ternaryRegularEquiv.prodCongr (MulEquiv.refl _)

def TernaryPhysicalPredicate (P : Subgroup (TernaryCyclic × Equiv.Perm Z) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm Z)) : Prop :=
  ∃ h : TernarySurvivingGraphs P,
    h.1.map ternaryPhysicalCoordinateEquiv.toMonoidHom = H

/-- The displayed physical triple is full for every accepted graph. -/
theorem ternaryPhysical_full
    (P : Subgroup (TernaryCyclic × Equiv.Perm Z) → Prop)
    {H : Subgroup (ternaryRegularAction × Equiv.Perm Z)}
    (hH : TernaryPhysicalPredicate P H) :
    H.map (MonoidHom.fst ternaryRegularAction (Equiv.Perm Z)) = ⊤ := by
  obtain ⟨h,rfl⟩ := hH
  obtain ⟨d,hd⟩ := h.2
  have hf : h.1.map (MonoidHom.fst TernaryCyclic (Equiv.Perm Z)) = ⊤ := by
    rw [← hd]
    exact ternaryActualGraph_full d.1 d.2.1
  rw [Subgroup.map_map]
  have he : (MonoidHom.fst ternaryRegularAction (Equiv.Perm Z)).comp
      ternaryPhysicalCoordinateEquiv.toMonoidHom =
      ternaryRegularEquiv.toMonoidHom.comp (MonoidHom.fst TernaryCyclic (Equiv.Perm Z)) := rfl
  rw [he,← Subgroup.map_map,hf]
  exact Subgroup.map_top_of_surjective _ ternaryRegularEquiv.surjective

/-- The external regular triple is an actual orbit of the original group. -/
theorem ternaryPhysical_orbit
    (P : Subgroup (TernaryCyclic × Equiv.Perm Z) → Prop)
    {H : Subgroup (ternaryRegularAction × Equiv.Perm Z)}
    (hH : TernaryPhysicalPredicate P H) (x : TernaryCyclic) :
    MulAction.orbit (H.map (fusionOrbitAction ternaryRegularAction)) (Sum.inl x) =
      Set.range (Sum.inl : TernaryCyclic → TernaryCyclic ⊕ Z) :=
  fusionOrbitAction_orbit_eq ternaryRegularAction ternaryRegularAction_transitive
    ⟨H,ternaryPhysical_full P hH⟩ x

theorem ternaryPhysicalLocal_card [Finite Z]
    (P : Subgroup (TernaryCyclic × Equiv.Perm Z) → Prop) :
    letI := Fintype.ofFinite (Subgroup (Equiv.Perm Z))
    Nat.card {H // TernaryPhysicalPredicate P H} =
      ∑ K : Subgroup (Equiv.Perm Z),
        ternarySurvivingWeight (fun χ : PrimeCharacters 3 K => P (ternaryActualGraph ⟨K,χ⟩)) := by
  let e := Equiv.ofInjective
    (fun h : TernarySurvivingGraphs P => h.1.map ternaryPhysicalCoordinateEquiv.toMonoidHom)
    (fun _ _ h => Subtype.ext (Subgroup.map_injective ternaryPhysicalCoordinateEquiv.injective h))
  have hc : Nat.card {H // TernaryPhysicalPredicate P H} = Nat.card (TernarySurvivingGraphs P) :=
    (Nat.card_congr e).symm
  rw [hc]
  exact ternarySurvivingGraphs_card P

/-- The original n!/(6 m!) row applied to the actual split-character family.
The surviving character moment is evaluated on its complete original source. -/
theorem ternaryPhysical_original_weight [Fintype Z]
    (P : Subgroup (TernaryCyclic × Equiv.Perm Z) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction (TernaryPhysicalPredicate P)) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction (TernaryPhysicalPredicate P)) : ℝ) ≤
      ((3+Fintype.card Z).factorial : ℝ) / (6*(Fintype.card Z).factorial) *
        ∑ K : Subgroup (Equiv.Perm Z),
          (ternarySurvivingWeight (fun χ : PrimeCharacters 3 K =>
            P (ternaryActualGraph ⟨K,χ⟩)) : ℝ) := by
  have h := fusionOrbitFamily_card_le ternaryRegularAction (TernaryPhysicalPredicate P) hP
  rw [ternaryRegularAction_normalizer_card,ternaryPhysicalLocal_card P] at h
  simpa only [TernaryCyclic,Fintype.card_multiplicative,ZMod.card, Nat.cast_sum,Nat.cast_ofNat,
    mul_comm (↑(Fintype.card Z).factorial : ℝ) (6:ℝ)] using h

end SymmetricSubgroupAsymptotics
