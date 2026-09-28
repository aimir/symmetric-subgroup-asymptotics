import SymmetricSubgroupAsymptotics.BinaryDisplacementCentralCut
import SymmetricSubgroupAsymptotics.Non2CentralCutNumerics

/-!
# The retained nonbinary annihilator cut

The full fixed-valued displacement image is a space of linear maps out of
the dual fixed space.  A general evaluation separator detects this whole
space on at most its dimension many inputs.  Its coannihilator therefore
contains a cut of the required dimension.  This gives the manuscript's
retained cut without choosing bases or pivot coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Every finite-dimensional subspace contains a subspace of each smaller
dimension.  The returned subspace lives in the original ambient space. -/
theorem exists_submodule_le_finrank_eq
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (Z : Submodule k V) (c : Nat) (hc : c ≤ Module.finrank k Z) :
    ∃ C : Submodule k V, C ≤ Z ∧ Module.finrank k C = c := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hc
  let u : Fin c → V := fun i => (v i : V)
  have hu : LinearIndependent k u :=
    hv.map' Z.subtype Z.ker_subtype
  refine ⟨Submodule.span k (Set.range u), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (v i).property
  · simpa only [Fintype.card_fin] using finrank_span_eq_card hu

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The literal retained cut in the original module.  Its dimension is
`min (t/2) (t-ell)`, its full displacement slice vanishes, and the fixed
dimension of the actual quotient is exactly `t-c`. -/
theorem exists_non2RetainedAnnihilatorCut
    (ρ : Representation (ZMod 2) G A) :
    let t := Module.finrank (ZMod 2) ρ.invariants
    let ell := Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) A // C ≤ ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (centralQuotientRepresentation ρ C.1 C.2).invariants =
        t - non2CentralCutDimension t ell := by
  classical
  let t := Module.finrank (ZMod 2) ρ.invariants
  let ell := Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)
  let L := (fixedDisplacementTranspose 2 ρ).range
  obtain ⟨W, hW, hsep⟩ :=
    LinearMapEvaluationSeparator.exists_separator_subspace_le_finrank L
  have hL : Module.finrank (ZMod 2) L = ell :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm
  rw [hL] at hW
  let Z := fixedDualCut ρ W
  have hZdim : t - ell ≤ Module.finrank (ZMod 2) Z := by
    have hsum := fixedDualCut_finrank_add ρ W
    change Module.finrank (ZMod 2) Z + Module.finrank (ZMod 2) W = t at hsum
    omega
  let c := non2CentralCutDimension t ell
  have hc : c ≤ Module.finrank (ZMod 2) Z :=
    (min_le_right (t / 2) (t - ell)).trans hZdim
  obtain ⟨C, hCZ, hCdim⟩ := exists_submodule_le_finrank_eq Z c hc
  have hCI : C ≤ ρ.invariants := hCZ.trans (fixedDualCut_le_invariants ρ W)
  have hZslice : displacementSlice ρ Z = ⊥ :=
    fixedDualCut_displacement_eq_bot ρ W hsep
  have hCslice : displacementSlice ρ C = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    have hfZ : f ∈ displacementSlice ρ Z :=
      ⟨hf.1, fun g => hCZ (hf.2 g)⟩
    rw [hZslice] at hfZ
    exact hfZ
  refine ⟨⟨C, hCI⟩, hCdim, hCslice, ?_⟩
  rw [centralQuotient_invariants_finrank_of_slice_eq_bot ρ C hCI hCslice,
    hCdim]

end SymmetricSubgroupAsymptotics

end
