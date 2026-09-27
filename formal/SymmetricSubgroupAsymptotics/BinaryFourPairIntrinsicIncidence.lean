import SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicCoverage

/-!
# The intrinsic noncritical four-frame incidence

The selector is the finite image of the actual marked noncritical family.
This avoids any artificial multiplicity cutoff.  Source coverage and target
ownership then turn the selected-profile Hall theorem into an inequality for
the whole intrinsic family.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicIncidence

open BinaryFourPairHallIncidence BinaryFourPairIntrinsicTarget
  BinaryFourPairIntrinsicCoverage

abbrev MarkedFamily (N : ℕ) :=
  Σ H : NoncriticalBinarySubgroups N,
    PermutationPairOrbitCharacters.Frame H.val 4

def selectedProfile (N : ℕ) (z : MarkedFamily N) : ResidualProfile N :=
  Classical.choose (exists_source_profile N z.1 z.2)

theorem selectedProfile_size (N : ℕ) (z : MarkedFamily N) :
    BinaryFourPairProfileUnion.ProfileSize
      (BinaryResidualOrbitMenu.points (2*N)) N (selectedProfile N z) :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).1

theorem selectedProfile_noncritical (N : ℕ) (z : MarkedFamily N) :
    HasNoncriticalResidual N (selectedProfile N z) :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).2.1

theorem selectedProfile_full (N : ℕ) (z : MarkedFamily N) :
    ∃ e : OrbitProfilePoints (Points N)
        (BinaryFourPairProfileUnion.sourceMultiplicity (selectedProfile N z)) ≃
        Fin (2*N),
      OrbitProfileFullOn (Action N) e z.1.val :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).2.2

/-- Finite selector consisting exactly of profiles needed by actual marked
intrinsic subgroups. -/
def selector (N : ℕ) : Finset (ResidualProfile N) :=
  Finset.univ.image (selectedProfile N)

theorem selector_size (N : ℕ) (t : ResidualProfile N)
    (ht : t ∈ selector N) :
    BinaryFourPairProfileUnion.ProfileSize
      (BinaryResidualOrbitMenu.points (2*N)) N t := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_size N z

theorem selector_noncritical (N : ℕ) (t : ResidualProfile N)
    (ht : t ∈ selector N) : HasNoncriticalResidual N t := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_noncritical N z

def sourceOfMarked (N : ℕ) (z : MarkedFamily N) :
    SourceFamily N (selector N) := by
  let e := Classical.choose (selectedProfile_full N z)
  have hOn := Classical.choose_spec (selectedProfile_full N z)
  let K := relabelSubgroup e.symm z.1.val
  have hKOn : OrbitProfileFullOn (Action N) (Equiv.refl _) K := by
    simpa only [e,Equiv.self_trans_symm] using hOn.relabel e.symm
  have hK : OrbitProfileFull (Action N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  refine ⟨z.1.val,?_⟩
  refine ⟨⟨selectedProfile N z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩,
    e,K,hK,?_⟩
  exact relabelSubgroup_symm e.symm z.1.val

@[simp] theorem sourceOfMarked_val (N : ℕ) (z : MarkedFamily N) :
    (sourceOfMarked N z).val = z.1.val := rfl

def sourceFrame (N : ℕ) (z : MarkedFamily N) :
    PermutationPairOrbitCharacters.Frame (sourceOfMarked N z).val 4 := by
  rw [sourceOfMarked_val]
  exact z.2

def markedEmbedding (N : ℕ) :
    MarkedFamily N ↪
      (Σ H : SourceFamily N (selector N),
        PermutationPairOrbitCharacters.Frame H.val 4) where
  toFun z := ⟨sourceOfMarked N z,sourceFrame N z⟩
  inj' := by
    rintro ⟨H,v⟩ ⟨K,w⟩ h
    have hp := Sigma.mk.inj_iff.mp h
    have hHK : H = K := by
      apply Subtype.ext
      calc
        H.val = (sourceOfMarked N ⟨H,v⟩).val := (sourceOfMarked_val N ⟨H,v⟩).symm
        _ = (sourceOfMarked N ⟨K,w⟩).val := congrArg Subtype.val hp.1
        _ = K.val := sourceOfMarked_val N ⟨K,w⟩
    exact Sigma.ext hHK (by
      simpa only [sourceFrame,sourceOfMarked_val] using hp.2)

local instance sourceFinite (N : ℕ) : Finite (SourceFamily N (selector N)) :=
  Finite.of_injective
    (fun H : SourceFamily N (selector N) =>
      (H.val : Set (Equiv.Perm (Fin (2*N)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

/-- Every intrinsic marked pair lies in the selected Hall source, without
identifying or quotienting its frame. -/
theorem intrinsic_frame_sum_le_source (N : ℕ) :
    ∑ H : NoncriticalBinarySubgroups N,
        Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) ≤
      ∑ H : SourceFamily N (selector N),
        Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) := by
  have h := Nat.card_le_card_of_injective (markedEmbedding N)
    (markedEmbedding N).injective
  simpa only [Nat.card_sigma] using h

theorem selected_source_frame_incidence (N : ℕ) :
    (∑ H : SourceFamily N (selector N),
        (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) ≤
      6*N * (Nat.card (NoncriticalBinarySubgroups N) : ℚ) := by
  have hhall := BinaryFourPairHallIncidence.selected_frame_incidence
    N (selector N) (selector_size N)
  have hfactorial : (0 : ℚ) < (2*N).factorial := by positivity
  have hcancel :
      (∑ H : SourceFamily N (selector N),
          (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) ≤
        6*N * (Nat.card (TargetFamily N (selector N)) : ℚ) := by
    apply (div_le_div_iff_of_pos_right hfactorial).mp
    calc
      (∑ H : SourceFamily N (selector N),
          (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) /
            (2*N).factorial ≤
          6*N * ((Nat.card (TargetFamily N (selector N)) : ℚ) /
            (2*N).factorial) := hhall
      _ = (6*N * (Nat.card (TargetFamily N (selector N)) : ℚ)) /
            (2*N).factorial := by ring
  have htargetNat := target_card_le_noncritical N (selector N)
    (selector_noncritical N)
  have htarget : (Nat.card (TargetFamily N (selector N)) : ℚ) ≤
      Nat.card (NoncriticalBinarySubgroups N) := by
    exact_mod_cast htargetNat
  exact hcancel.trans (mul_le_mul_of_nonneg_left htarget (by positivity))

/-- Complete numerical Hall incidence on the intrinsic noncritical binary
family.  Both the selected source and every target are forgotten only after
their literal original-action profiles have been checked. -/
theorem intrinsic_four_frame_incidence (N : ℕ) :
    (∑ H : NoncriticalBinarySubgroups N,
        (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) ≤
      6*N * (Nat.card (NoncriticalBinarySubgroups N) : ℚ) := by
  have hcoverNat := intrinsic_frame_sum_le_source N
  have hcover :
      (∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) ≤
        ∑ H : SourceFamily N (selector N),
          (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ) := by
    exact_mod_cast hcoverNat
  exact hcover.trans (selected_source_frame_incidence N)

end SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicIncidence

end
