import SymmetricSubgroupAsymptotics.C3TrivialLowNormalized
import SymmetricSubgroupAsymptotics.FusionPhysicalUnion

/-!
# Complete regular-C3 physical frontier

The full regular-C3 local family is covered by three exhaustive branches:
the direct axis, the low-rank trivial axis, and the high-rank trivial axis.
The first two have checked contracting original-weight rows.  The final
branch is isolated as the sole remaining degree-three physical obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

def C3TrivialHighPredicate (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  FusionAcceptedOrbitPredicate ternaryRegularAction P H ∧
    H.goursatFst = ⊥ ∧
      3*b < 20*ternaryCharacterRank
        (H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b))))

theorem c3TrivialHighPredicate_natural (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    FusionOrbitNatural ternaryRegularAction (C3TrivialHighPredicate b P) := by
  rintro c H ⟨⟨hfull,hPs⟩,haxis,hrank⟩
  refine ⟨⟨fusion_full_map_prod H hfull
    (ternaryRegularAction.normalizerMonoidHom c.1) (MulAut.conj c.2),
      hP c H hPs⟩,?_,?_⟩
  · change (H.map (((ternaryRegularAction.normalizerMonoidHom c.1).prodCongr
      (MulAut.conj c.2)).toMonoidHom)).goursatFst = ⊥
    rw [fusion_axis_map_prod,haxis]
    exact Subgroup.map_bot _
  · change 3*b < 20*ternaryCharacterRank
      ((H.map (((ternaryRegularAction.normalizerMonoidHom c.1).prodCongr
        (MulAut.conj c.2)).toMonoidHom)).map
          (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b))))
    rw [fusion_complement_map_prod,ternaryCharacterRank_map_conj]
    exact hrank

inductive C3PhysicalBranch
  | direct
  | low
  | high
  deriving DecidableEq, Fintype

def c3PhysicalBranchFamily (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    C3PhysicalBranch → Set (Subgroup
      (Equiv.Perm (TernaryCyclic ⊕ Fin b)))
  | .direct => FusionOrbitFamily ternaryRegularAction
      (C3DirectAxisPredicate b P)
  | .low => FusionOrbitFamily ternaryRegularAction
      (C3TrivialLowPredicate b P)
  | .high => FusionOrbitFamily ternaryRegularAction
      (C3TrivialHighPredicate b P)

private theorem c3Accepted_local_three_way (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : FusionAcceptedOrbitPredicate ternaryRegularAction P H) :
    C3DirectAxisPredicate b P H ∨ C3TrivialLowPredicate b P H ∨
      C3TrivialHighPredicate b P H := by
  rcases ternaryRegularAction_subgroup_eq_bot_or_top H.goursatFst with haxis | haxis
  · by_cases hrank : 20*ternaryCharacterRank
        (H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin b)))) ≤ 3*b
    · exact Or.inr (Or.inl ⟨⟨hH.1,hH.2,hrank⟩,haxis⟩)
    · exact Or.inr (Or.inr ⟨hH,haxis,by omega⟩)
  · exact Or.inl ⟨hH,haxis⟩

/-- A local three-way cover induces a cover of the complete labelled
physical families; the same label change is retained. -/
theorem c3Accepted_physical_three_way_cover (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (K : Subgroup (Equiv.Perm (TernaryCyclic ⊕ Fin b)))
    (hK : K ∈ FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction P)) :
    ∃ i : C3PhysicalBranch, K ∈ c3PhysicalBranchFamily b P i := by
  obtain ⟨⟨e,⟨M,hM⟩⟩,rfl⟩ := hK
  obtain ⟨H,hH,rfl⟩ := hM
  rcases c3Accepted_local_three_way b P H.1 H.2 with hd | hl | hh
  · refine ⟨C3PhysicalBranch.direct,⟨⟨e,⟨H.1.map
        (fusionOrbitAction ternaryRegularAction),?_⟩⟩,rfl⟩⟩
    exact ⟨⟨H.1,hd⟩,rfl⟩
  · refine ⟨C3PhysicalBranch.low,⟨⟨e,⟨H.1.map
        (fusionOrbitAction ternaryRegularAction),?_⟩⟩,rfl⟩⟩
    exact ⟨⟨H.1,hl⟩,rfl⟩
  · refine ⟨C3PhysicalBranch.high,⟨⟨e,⟨H.1.map
        (fusionOrbitAction ternaryRegularAction),?_⟩⟩,rfl⟩⟩
    exact ⟨⟨H.1,hh⟩,rfl⟩

private theorem finitePhysicalUnion_card_le {ι X : Type*} [Fintype ι] [Finite X]
    (F : Set (Subgroup (Equiv.Perm X)))
    (A : ι → Set (Subgroup (Equiv.Perm X)))
    (hcover : ∀ H∈F, ∃ i, H∈A i) :
    Nat.card F ≤ ∑ i, Nat.card (A i) := by
  let B : Set (Subgroup (Equiv.Perm X)) := {H | ∃ i, H∈A i}
  have hFB : Nat.card F ≤ Nat.card B := Nat.card_le_card_of_injective
    (fun H : F => (⟨H.1,hcover H.1 H.2⟩ : B))
    (fun x y he => Subtype.ext (congrArg (fun z : B => z.1) he))
  let f : (Σ i, A i) → B := fun d => ⟨d.2.1,⟨d.1,d.2.2⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨H,i,hi⟩
    exact ⟨⟨i,H,hi⟩,rfl⟩
  have hBA := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sigma] at hBA
  exact hFB.trans hBA

theorem c3Accepted_physical_three_way_card_le (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction P)) ≤
      Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3DirectAxisPredicate b P)) +
      Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3TrivialLowPredicate b P)) +
      Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3TrivialHighPredicate b P)) := by
  have h := finitePhysicalUnion_card_le
    (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction P))
    (c3PhysicalBranchFamily b P)
    (c3Accepted_physical_three_way_cover b P)
  calc
    _ ≤ ∑ i : C3PhysicalBranch,
        Nat.card (c3PhysicalBranchFamily b P i) := h
    _ = _ := by
      rw [show (Finset.univ : Finset C3PhysicalBranch) =
        {C3PhysicalBranch.direct,C3PhysicalBranch.low,C3PhysicalBranch.high} by decide]
      rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [c3PhysicalBranchFamily]
      omega

def c3TrivialHighRatio (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) : ℝ :=
  (Nat.card (FusionOrbitFamily ternaryRegularAction
    (C3TrivialHighPredicate b P)):ℝ)/exactBenchmark (b+3)

theorem c3TrivialHighRatio_nonneg (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop) :
    0 ≤ c3TrivialHighRatio b P := by
  unfold c3TrivialHighRatio
  exact div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le

/-- The sole unresolved regular-C3 term is the high-rank trivial-axis ratio.
Both completed branches keep the complete lower-degree subgroup count. -/
theorem c3Accepted_physical_frontier (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction P) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction P)):ℝ) /
        exactBenchmark (b+3) ≤
      (c3DirectAxisKernel b+c3TrivialLowKernel b)*
        ((subgroupCount b:ℝ)/exactBenchmark b) + c3TrivialHighRatio b P := by
  have hc : (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction P)):ℝ) ≤
      (Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3DirectAxisPredicate b P)):ℝ) +
      (Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3TrivialLowPredicate b P)):ℝ) +
      (Nat.card (FusionOrbitFamily ternaryRegularAction
        (C3TrivialHighPredicate b P)):ℝ) := by
    exact_mod_cast c3Accepted_physical_three_way_card_le b P
  have hN := exactBenchmark_pos (b+3)
  have hdiv := div_le_div_of_nonneg_right hc hN.le
  have hd := c3DirectAxis_physical_normalized b P hP
  have hl := c3TrivialLow_physical_normalized b P hP
  unfold c3TrivialHighRatio
  calc
    _ ≤ (_+_+_)/exactBenchmark (b+3) := hdiv
    _ = _/exactBenchmark (b+3)+_/exactBenchmark (b+3)+
        _/exactBenchmark (b+3) := by ring
    _ ≤ c3DirectAxisKernel b*((subgroupCount b:ℝ)/exactBenchmark b)+
        c3TrivialLowKernel b*((subgroupCount b:ℝ)/exactBenchmark b)+
        (Nat.card (FusionOrbitFamily ternaryRegularAction
          (C3TrivialHighPredicate b P)):ℝ)/exactBenchmark (b+3) :=
      add_le_add (add_le_add hd hl) le_rfl
    _ = _ := by ring

end SymmetricSubgroupAsymptotics

end
