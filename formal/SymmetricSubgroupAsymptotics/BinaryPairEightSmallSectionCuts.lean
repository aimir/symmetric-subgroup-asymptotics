import SymmetricSubgroupAsymptotics.BinaryDisplacementCentralCut
import SymmetricSubgroupAsymptotics.BinaryPairSection

/-!
# Small actual sections on an eight-pair frame

A full displacement separator of dimension at most the displacement
dimension gives an actual central cut of cost at most twice the original
section dimension. In particular every section of dimension at most three
has cost at most six, giving a strict gap at pair degree eight.

The argument retains the complete original displacement space and the
literal original quotient action. No action catalogue, character-line
bound, or supplied capacity certificate is needed. Sections of dimension
four are outside the strict six-cost conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
open LinearMapEvaluationSeparator

section Representation

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A)

/-- A full separator gives a literal annihilator cut with cost at most
twice the original representation dimension. No permutation realization
is required for this linear bound. -/
theorem binary_representation_exists_central_cut_twice_finrank :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧
      2*Module.finrank (ZMod 2) C +
        4*Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants ≤
          2*Module.finrank (ZMod 2) A := by
  let t := Module.finrank (ZMod 2) ρ.invariants
  let ell := Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)
  let L := (fixedDisplacementTranspose 2 ρ).range
  have hL : Module.finrank (ZMod 2) L=ell :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm
  obtain ⟨W,hW,hsep⟩ := exists_separator_subspace_le_finrank L
  refine ⟨fixedDualCut ρ W,fixedDualCut_le_invariants ρ W,
    fixedDualCut_displacement_eq_bot ρ W hsep,?_⟩
  rw [fixedDualCut_quotient_invariants_finrank ρ W hsep]
  have hcut := fixedDualCut_finrank_add ρ W
  have heA : t+ell≤Module.finrank (ZMod 2) A := by
    have he := Submodule.finrank_le
      (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants
    rw [← displacementSlice_invariants_finrank] at he
    have hdim := ρ.invariants.finrank_quotient_add_finrank
    change ell≤Module.finrank (ZMod 2) (A ⧸ ρ.invariants) at he
    omega
  rw [hL] at hW
  change Module.finrank (ZMod 2) (fixedDualCut ρ W)+Module.finrank (ZMod 2) W=t at hcut
  omega

/-- The same original cut has the corresponding actual Schur-capacity
bound when the acting group is binary. -/
theorem binary_representation_exists_central_cut_capacity_twice_finrank
    [Finite A] (hG : IsPGroup 2 G) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C +
        4*representationSchurCapacity (centralQuotientRepresentation ρ C hC) ≤
          2*Module.finrank (ZMod 2) A := by
  obtain ⟨C,hC,_,hcost⟩ := binary_representation_exists_central_cut_twice_finrank ρ
  letI : Finite (A ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  refine ⟨C,hC,?_⟩
  rw [pGroup_representationSchurCapacity hG]
  exact_mod_cast hcost

end Representation

namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- This uses the original acting quotient U/(ker(top) join N) directly.
Neither top transitivity nor a faithful action of that quotient is needed. -/
theorem exists_section_cut_cost_le_twice_finrank [Finite X] [Finite I]
    (hU : IsPGroup 2 U) :
    ∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC) ≤
          2*Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
  let A := F.kernelSpace ⧸ F.normalSpace N
  letI : Finite A :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  obtain ⟨C,hC,hcost⟩ := binary_representation_exists_central_cut_capacity_twice_finrank
    (F.sectionRepresentation N) (hU.to_quotient (F.top.ker⊔N))
  refine ⟨C,hC,?_⟩
  exact hcost

/-- Every literal section of dimension at most three has an actual cut
of cost at most six. The normal remains a normal of the original U. -/
theorem exists_section_cut_of_finrank_le_three [Finite X] [Finite I]
    (hU : IsPGroup 2 U)
    (hsmall : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤3) :
    ∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)≤6 := by
  obtain ⟨C,hC,hcost⟩ := F.exists_section_cut_cost_le_twice_finrank N hU
  refine ⟨C,hC,hcost.trans ?_⟩
  have hs : (Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N):ℝ)≤3 := by
    exact_mod_cast hsmall
  linarith

/-- At eight actual pair labels the proved cut leaves a gap of at least
two in the pair-degree budget. This does not assert a dimension-four gap. -/
theorem exists_eight_small_section_cut [Finite X] [Finite I]
    (hU : IsPGroup 2 U) (hI : Nat.card I=8)
    (hsmall : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤3) :
    ∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)+2≤(Nat.card I:ℝ) := by
  obtain ⟨C,hC,hcost⟩ := F.exists_section_cut_of_finrank_le_three N hU hsmall
  refine ⟨C,hC,?_⟩
  rw [hI]
  norm_num only [Nat.cast_ofNat]
  linarith

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
