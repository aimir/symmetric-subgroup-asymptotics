import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualEquivalence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane

/-! Reversible original-coordinate restriction/extension for Q-singular
D4 subspaces containing the original root plane. Every negative-head
equation is derived from Q-singularity and actual root-plane inclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexQuadraticNeighborPlane
variable (K : Type) [Field K]

def restriction (M : Submodule K (Index 4 → K)) : Submodule K (Index 2 → K) :=
  M.map (twiceTailRestriction K 2)

theorem negative_heads_zero (M : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) (hR : rootPlane K ≤ M)
    (x : Index 4 → K) (hx : x ∈ M) :
    x (Sum.inr 0) = 0 ∧ x (Sum.inr (tailSecondIndex 2)) = 0 := by
  have h0 : head0 K ∈ M := hR (Submodule.subset_span (Or.inl rfl))
  have h1 : head1 K ∈ M := hR (Submodule.subset_span (Or.inr rfl))
  have hp0 := polar_zero_of_singular (splitQuadraticForm K 4) M hM (head0 K) x h0 hx
  have hp1 := polar_zero_of_singular (splitQuadraticForm K 4) M hM (head1 K) x h1 hx
  change (splitQuadraticForm K 4).polarBilin (Pi.single (Sum.inl (0 : Fin 4)) 1) x = 0 at hp0
  change (splitQuadraticForm K 4).polarBilin (Pi.single (Sum.inl (tailSecondIndex 2)) 1) x = 0 at hp1
  rw [positive_polar] at hp0 hp1
  exact ⟨hp0, hp1⟩

theorem restriction_singular (M : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) (hR : rootPlane K ≤ M) :
    ∀ z ∈ restriction K M, splitQuadraticForm K 2 z = 0 := by
  rintro z ⟨x, hx, rfl⟩
  have hh := negative_heads_zero K M hM hR x hx
  exact (quadratic_eq_tail_of_heads_zero K x hh.1 hh.2).symm.trans (hM x hx)

theorem le_extension_restriction (M : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) (hR : rootPlane K ≤ M) :
    M ≤ extension K (restriction K M) := by
  intro x hx
  have hh := negative_heads_zero K M hM hR x hx
  exact ⟨hh.1, hh.2, ⟨x, hx, rfl⟩⟩

theorem extension_restriction_le (M : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) (hR : rootPlane K ≤ M) :
    extension K (restriction K M) ≤ M := by
  have h0 : head0 K ∈ M := hR (Submodule.subset_span (Or.inl rfl))
  have h1 : head1 K ∈ M := hR (Submodule.subset_span (Or.inr rfl))
  intro v hv
  obtain ⟨x, hx, he⟩ := hv.2.2
  have hh := negative_heads_zero K M hM hR x hx
  have hdec := twice_head_tail_decomposition K 2 x hh.1 hh.2
  have hhead : x (Sum.inl 0) • head0 K + x (Sum.inl (tailSecondIndex 2)) • head1 K ∈ M :=
    M.add_mem (M.smul_mem _ h0) (M.smul_mem _ h1)
  have htailEq : x - (x (Sum.inl 0) • head0 K + x (Sum.inl (tailSecondIndex 2)) • head1 K) =
      twiceTailExtension K 2 (twiceTailRestriction K 2 x) := by
    calc
      _ = (x (Sum.inl 0) • head0 K + x (Sum.inl (tailSecondIndex 2)) • head1 K +
          twiceTailExtension K 2 (twiceTailRestriction K 2 x)) -
          (x (Sum.inl 0) • head0 K + x (Sum.inl (tailSecondIndex 2)) • head1 K) :=
        congrArg (fun z => z - (x (Sum.inl 0) • head0 K + x (Sum.inl (tailSecondIndex 2)) • head1 K)) hdec
      _ = _ := by abel
  have htail : twiceTailExtension K 2 (twiceTailRestriction K 2 x) ∈ M :=
    htailEq ▸ M.sub_mem hx hhead
  have hvdec := twice_head_tail_decomposition K 2 v hv.1 hv.2.1
  have hvmem : v (Sum.inl 0) • head0 K + v (Sum.inl (tailSecondIndex 2)) • head1 K +
      twiceTailExtension K 2 (twiceTailRestriction K 2 v) ∈ M := by
    apply M.add_mem (M.add_mem (M.smul_mem _ h0) (M.smul_mem _ h1))
    rw [← he]
    exact htail
  exact hvdec.symm ▸ hvmem

theorem extension_restriction_eq (M : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) (hR : rootPlane K ≤ M) :
    extension K (restriction K M) = M :=
  le_antisymm (extension_restriction_le K M hM hR) (le_extension_restriction K M hM hR)

theorem restriction_extension_eq (L : Submodule K (Index 2 → K)) : restriction K (extension K L) = L := by
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact hx.2.2
  · intro z hz
    exact ⟨twiceTailExtension K 2 z, twiceTail_mem_extension K L z hz, twiceTail_leftInverse K 2 z⟩

theorem restriction_finrank_of_four (M : Submodule K (Index 4 → K))
    (hd : Module.finrank K M = 4) (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0)
    (hR : rootPlane K ≤ M) : Module.finrank K (restriction K M) = 2 := by
  have hh := extension_finrank K (restriction K M)
  rw [extension_restriction_eq K M hM hR, hd] at hh
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
