import SymmetricSubgroupAsymptotics.BinaryPairRankThreeResidual
import SymmetricSubgroupAsymptotics.BinaryPairEightLargeSectionCharacter

/-! Complete reduction of original eight-pair axes to a strict actual
cut, actual small source/target orders, the original character criterion,
or the explicitly retained rank-two residual. The last family is not
asserted to be accepted or identified with any carrier catalogue.

The full separator gives a literal cut whose cost is simultaneously
bounded by 4t and 2t+2ell. Thus dimension four leaves only (3,1) and
(2,2), and the actual original-action adapters handle those branches.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open LinearMapEvaluationSeparator

section SeparatorCost

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A)

/-- The separator is a subspace of the full original fixed dual as
well as having dimension at most the complete displacement dimension. -/
theorem binary_representation_exists_central_cut_min_cost :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧
      2*Module.finrank (ZMod 2) C+
        4*Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants≤
      min (4*Module.finrank (ZMod 2) ρ.invariants)
        (2*Module.finrank (ZMod 2) ρ.invariants+
          2*Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) := by
  let L := (fixedDisplacementTranspose 2 ρ).range
  have hL : Module.finrank (ZMod 2) L=
      Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants) :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm
  obtain ⟨W,hW,hsep⟩ := exists_separator_subspace_le_finrank L
  have hWt : Module.finrank (ZMod 2) W≤Module.finrank (ZMod 2) ρ.invariants := by
    simpa only [Subspace.dual_finrank_eq] using Submodule.finrank_le W
  rw [hL] at hW
  have hcut := fixedDualCut_finrank_add ρ W
  refine ⟨fixedDualCut ρ W,fixedDualCut_le_invariants ρ W,
    fixedDualCut_displacement_eq_bot ρ W hsep,?_⟩
  rw [fixedDualCut_quotient_invariants_finrank ρ W hsep]
  omega

/-- The same original cut has this bound for its actual Schur capacity.
No capacity bound or supplied separator is an input. -/
theorem binary_representation_exists_central_cut_capacity_min_cost
    [Finite A] (hG : IsPGroup 2 G) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (centralQuotientRepresentation ρ C hC)≤
      (min (4*Module.finrank (ZMod 2) ρ.invariants)
        (2*Module.finrank (ZMod 2) ρ.invariants+
          2*Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) : ℕ) := by
  obtain ⟨C,hC,_,hcost⟩ := binary_representation_exists_central_cut_min_cost ρ
  letI : Finite (A ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  refine ⟨C,hC,?_⟩
  rw [pGroup_representationSchurCapacity hG]
  exact_mod_cast hcost

end SeparatorCost

namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- This residual retains the actual dimensions, original top kernel,
its original point orbits, and the entire top image of the original N. -/
def EightPairRankTwoResidual : Prop :=
  Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4 ∧
  Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants=2 ∧
  Module.finrank (ZMod 2) (centralQuotientRepresentation (F.sectionRepresentation N)
    (F.sectionRepresentation N).invariants le_rfl).invariants=2 ∧
  Nonempty (RepresentationBinaryCommonCharacter.TwoBlockCharacter
    (F.sectionTopRepresentation N)) ∧
  Nat.card (MulAction.orbitRel.Quotient (F.sectionTopRepresentation N).ker I)=2 ∧
  (∀ o : MulAction.orbitRel.Quotient (F.sectionTopRepresentation N).ker I,
    Nat.card o.orbit=4) ∧
  N.map F.top.rangeRestrict≤(F.sectionTopRepresentation N).ker

/-- A reduction conclusion, not a carrier-acceptance certificate. -/
def EightPairAxisReduction : Prop :=
  (∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
    (hC : C≤(F.sectionRepresentation N).invariants),
    (2:ℝ)*Module.finrank (ZMod 2) C+
      4*representationSchurCapacity (F.cutRepresentation N C hC)≤6) ∨
  (Nat.card U≤256 ∧ Nat.card (U ⧸ N)≤128) ∨
  Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) ∨
  F.EightPairRankTwoResidual N

/-- Every original dimension-four axis reduces through actual cuts,
original orders and characters, leaving only the specified two-block
original residual. All statements refer to the same normal N. -/
theorem eight_dimension_four_reduction [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4) :
    F.EightPairAxisReduction N := by
  classical
  let t := Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants
  let ell := Module.finrank (ZMod 2)
    (centralQuotientRepresentation (F.sectionRepresentation N)
      (F.sectionRepresentation N).invariants le_rfl).invariants
  have ht : t≤3 := F.section_invariants_finrank_le_three_of_eight N hU hI
  have hsum : t+ell≤4 := by
    have he := Submodule.finrank_le
      (centralQuotientRepresentation (F.sectionRepresentation N)
        (F.sectionRepresentation N).invariants le_rfl).invariants
    have hq := (F.sectionRepresentation N).invariants.finrank_quotient_add_finrank
    change ell≤Module.finrank (ZMod 2)
      ((F.kernelSpace ⧸ F.normalSpace N) ⧸ (F.sectionRepresentation N).invariants) at he
    change Module.finrank (ZMod 2)
      ((F.kernelSpace ⧸ F.normalSpace N) ⧸ (F.sectionRepresentation N).invariants)+t=
        Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) at hq
    omega
  by_cases hthree : t=3 ∧ ell=1
  · rcases F.eight_rank_three_order_or_character N hU hI hd hthree.1 with horder | hchar
    · exact Or.inr (Or.inl horder)
    · exact Or.inr (Or.inr (Or.inl hchar))
  by_cases htwo : t=2 ∧ ell=2
  · rcases F.eight_rank_two_cut_or_original_kernel N hU hI hd htwo.1 htwo.2 with hcut | hkernel
    · exact Or.inl hcut
    · exact Or.inr (Or.inr (Or.inr ⟨hd,htwo.1,htwo.2,hkernel⟩))
  have hsmall : min (4*t) (2*t+2*ell)≤6 := by omega
  obtain ⟨C,hC,hcost⟩ := binary_representation_exists_central_cut_capacity_min_cost
    (F.sectionRepresentation N) (hU.to_quotient (F.top.ker⊔N))
  rw [displacementSlice_invariants_finrank] at hcost
  change (2:ℝ)*Module.finrank (ZMod 2) C+
    4*representationSchurCapacity (F.cutRepresentation N C hC)≤(min (4*t) (2*t+2*ell):ℕ) at hcost
  have hsmall' : ((min (4*t) (2*t+2*ell):ℕ):ℝ)≤6 := by exact_mod_cast hsmall
  exact Or.inl ⟨C,hC,hcost.trans hsmall'⟩

/-- The complete original eight-pair reduction has no section-dimension
premise and no assumed carrier-completeness statement. -/
theorem eight_section_residual_reduction [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8) : F.EightPairAxisReduction N := by
  rcases F.eight_section_cut_or_character_or_dimension_four N hU hI with hcut | hchar | hfour
  · obtain ⟨C,hC,hcost⟩ := hcut
    apply Or.inl
    refine ⟨C,hC,?_⟩
    rw [hI] at hcost
    norm_num only [Nat.cast_ofNat] at hcost
    linarith
  · exact Or.inr (Or.inr (Or.inl hchar))
  · exact F.eight_dimension_four_reduction N hU hI hfour

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
