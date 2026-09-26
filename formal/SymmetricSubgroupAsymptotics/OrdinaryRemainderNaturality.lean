import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly
import SymmetricSubgroupAsymptotics.FusionOrbitPointing
import SymmetricSubgroupAsymptotics.FiniteFirstOwnership

/-! Relabelling preserves the complete critical family and its literal
complement. The odd branch retains both the singleton and full natural S3
marker, with the original positive-rank guard. A physical invariant predicate
pulls back through the actual orbit action and its complete complement to
original-normalizer naturality. No owner cover or counting bound is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

universe u v

/-- Change only the physical labels. The same profile, model subgroup and
entire model predicate witness membership in the relabelled family. -/
def assembledOrbitProfilesOnRelabel {τ ι X Y : Type*} {Ω : ι → Type*}
    (m : τ → ι → ℕ)
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop)
    (e : X ≃ Y) (H : AssembledOrbitProfilesOn m P X) :
    AssembledOrbitProfilesOn m P Y :=
  ⟨relabelSubgroup e H.1, by
    obtain ⟨t,f,K,hK,hH⟩ := H.2
    refine ⟨t,f.trans e,K,hK,?_⟩
    rw [← relabelSubgroup_trans,hH]⟩

/-- Relabel every full critical lift in the same parity branch. The odd
profile index is unchanged, including its full marker and rank guard. -/
def criticalSubgroupRelabel (n : ℕ) (e : Equiv.Perm (Fin n)) :
    CriticalSubgroups n → CriticalSubgroups n := by
  unfold CriticalSubgroups
  split <;> exact assembledOrbitProfilesOnRelabel _ _ e

/-- Transport both maps across the same type equality. This handles the
casts introduced by the two existing parity splits without reducing them. -/
private theorem embedding_cast_compatible {A B : Type u} {X : Type v} (h : A = B)
    (j : B ↪ X) (f : B → B) (g : X → X)
    (hf : ∀ b, j (f b) = g (j b)) :
    ∀ a : A,
      (Eq.mpr (congrArg (fun T => T ↪ X) h) j)
        ((Eq.mpr (congrArg (fun T => T → T) h) f) a) =
      g ((Eq.mpr (congrArg (fun T => T ↪ X) h) j) a) := by
  cases h
  exact hf

@[simp] theorem criticalSubgroupRelabel_val (n : ℕ) (e : Equiv.Perm (Fin n))
    (H : CriticalSubgroups n) :
    criticalSubgroupEmbedding n (criticalSubgroupRelabel n e H) =
      relabelSubgroup e (criticalSubgroupEmbedding n H) := by
  revert H
  by_cases hn : n % 2 = 0
  · have hdec : instDecidableEqNat (n % 2) 0 = Decidable.isTrue hn :=
      Subsingleton.elim _ _
    have htype : CriticalSubgroups n = EvenCriticalSubgroupsOn (n / 2) n :=
      if_pos hn
    have hcompat := embedding_cast_compatible htype
      (⟨Subtype.val,Subtype.val_injective⟩ :
        EvenCriticalSubgroupsOn (n / 2) n ↪ Subgroup (Equiv.Perm (Fin n)))
      (assembledOrbitProfilesOnRelabel _ _ e) (relabelSubgroup e) (fun _ => rfl)
    simp only [criticalSubgroupEmbedding,criticalSubgroupRelabel,CriticalSubgroups,hdec]
    exact hcompat
  · have hdec : instDecidableEqNat (n % 2) 0 = Decidable.isFalse hn :=
      Subsingleton.elim _ _
    have htype : CriticalSubgroups n = OddCriticalSubgroupsOn (n / 2) n :=
      if_neg hn
    have hcompat := embedding_cast_compatible htype
      (⟨Subtype.val,Subtype.val_injective⟩ :
        OddCriticalSubgroupsOn (n / 2) n ↪ Subgroup (Equiv.Perm (Fin n)))
      (assembledOrbitProfilesOnRelabel _ _ e) (relabelSubgroup e) (fun _ => rfl)
    simp only [criticalSubgroupEmbedding,criticalSubgroupRelabel,CriticalSubgroups,hdec]
    exact hcompat

theorem isCriticalSubgroup_relabel (n : ℕ) (e : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : IsCriticalSubgroup n H) :
    IsCriticalSubgroup n (relabelSubgroup e H) := by
  obtain ⟨K,rfl⟩ := hH
  exact ⟨criticalSubgroupRelabel n e K,criticalSubgroupRelabel_val n e K⟩

/-- The complete critical condition, in either parity, is invariant under
actual permutation conjugacy. This also covers degrees zero and one. -/
theorem isCriticalSubgroup_relabel_iff (n : ℕ) (e : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n))) :
    IsCriticalSubgroup n (relabelSubgroup e H) ↔ IsCriticalSubgroup n H := by
  constructor
  · intro hH
    simpa only [relabelSubgroup_symm] using
      isCriticalSubgroup_relabel n e.symm (relabelSubgroup e H) hH
  · exact isCriticalSubgroup_relabel n e H

theorem ordinaryRemainder_relabel_iff (n : ℕ) (e : Equiv.Perm (Fin n))
    (H : Subgroup (Equiv.Perm (Fin n))) :
    (¬ IsCriticalSubgroup n (relabelSubgroup e H)) ↔ ¬ IsCriticalSubgroup n H :=
  not_congr (isCriticalSubgroup_relabel_iff n e H)

/-- A relabelling-invariant predicate of actual physical subgroups is natural
under the original action normalizer and every relabelling of the complete
complement. The supplied point equivalence is used on the entire subgroup. -/
theorem fusionOrbitNatural_of_relabel_invariant {Ω Z X : Type*}
    (U : Subgroup (Equiv.Perm Ω)) (e : Ω ⊕ Z ≃ X)
    (P : Subgroup (Equiv.Perm X) → Prop)
    (hP : ∀ (s : Equiv.Perm X) (K : Subgroup (Equiv.Perm X)),
      P (relabelSubgroup s K) ↔ P K) :
    FusionOrbitNatural U (fun H =>
      P (relabelSubgroup e (H.map (fusionOrbitAction (Z := Z) U)))) := by
  intro c H hH
  rw [fusionOrbitAction_map_coordinateChange,relabelSubgroup_trans]
  let s : Equiv.Perm X := e.symm.trans ((fusionPointingSymmetryMap U c).trans e)
  have he : e.trans s = (fusionPointingSymmetryMap U c).trans e := by
    ext x
    simp only [s,Equiv.trans_apply,Equiv.symm_apply_apply]
  have h := (hP s (relabelSubgroup e (H.map (fusionOrbitAction U)))).mpr hH
  simpa only [relabelSubgroup_trans,he] using h

/-- The exact ordinary remainder condition on the full physical subgroup:
the original w-point action and the entire b-point complement stay present. -/
def ordinaryRemainderFusionPredicate {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (H : Subgroup (U × Equiv.Perm (Fin b))) : Prop :=
  ¬ IsCriticalSubgroup (w+b)
    (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
      (H.map (fusionOrbitAction (Z := Fin b) U)))

/-- The complete noncritical filter supplies its own naturality proof;
there is no binary-only or restricted odd-marker replacement. -/
theorem ordinaryRemainderFusionPredicate_natural {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) :
    FusionOrbitNatural U (ordinaryRemainderFusionPredicate (b := b) U) :=
  fusionOrbitNatural_of_relabel_invariant U
    (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
    (fun H => ¬ IsCriticalSubgroup (w+b) H)
    (fun s H => ordinaryRemainder_relabel_iff (w+b) s H)

/-- First ownership is assigned on the original physical subgroups, before
any local chart or labelling choices. Literal eligibility coverage remains
an explicit hypothesis; it is not supplied by the cardinality identity. -/
theorem ordinaryRemainder_firstOwnership_card (n : ℕ) {r : ℕ}
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hcover : ∀ H, ¬ IsCriticalSubgroup n H → ∃ i, Eligible i H) :
    Nat.card (OrdinaryRemainderSubgroups n) =
      ∑ i : Fin r, Nat.card {H : Subgroup (Equiv.Perm (Fin n)) //
        ¬ IsCriticalSubgroup n H ∧ FirstOwned Eligible i H} :=
  firstOwnership_card (fun H => ¬ IsCriticalSubgroup n H) Eligible hcover

/-- Every earlier exclusion survives actual physical relabelling. The
eligibility hypotheses refer to the full physical subgroups, not merely
to a normalizer-stable local presentation. -/
theorem ordinaryRemainder_firstOwned_relabel_iff (n : ℕ) {r : ℕ}
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin n)) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H)
    (i : Fin r) (s : Equiv.Perm (Fin n)) (H : Subgroup (Equiv.Perm (Fin n))) :
    (¬ IsCriticalSubgroup n (relabelSubgroup s H) ∧
      FirstOwned Eligible i (relabelSubgroup s H)) ↔
    (¬ IsCriticalSubgroup n H ∧ FirstOwned Eligible i H) :=
  and_congr (ordinaryRemainder_relabel_iff n s H)
    (firstOwned_transport_iff Eligible Eligible (relabelSubgroup s)
      (fun j K => (hEligible j s K).symm) i H).symm

/-- Pull back the actual physical first-owner predicate with every prior
exclusion intact. This naturality conclusion does not supply eligibility
coverage or identify the predicate with an intrinsic carrier family. -/
theorem ordinaryRemainder_firstOwnerFusion_natural {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H)
    (i : Fin r) :
    FusionOrbitNatural U (fun H => ordinaryRemainderFusionPredicate (b := b) U H ∧
      FirstOwned Eligible i
        (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
          (H.map (fusionOrbitAction (Z := Fin b) U)))) :=
  fusionOrbitNatural_of_relabel_invariant U
    (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
    (fun H => ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H)
    (fun s H => ordinaryRemainder_firstOwned_relabel_iff (w+b) Eligible hEligible i s H)

end SymmetricSubgroupAsymptotics
