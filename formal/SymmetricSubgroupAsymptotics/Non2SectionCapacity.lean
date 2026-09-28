import SymmetricSubgroupAsymptotics.Non2RetainedAnnihilatorCut
import SymmetricSubgroupAsymptotics.Non2CentralCutFusion
import SymmetricSubgroupAsymptotics.Non2CoupledSchurNumerics
import SymmetricSubgroupAsymptotics.Non2SchurTraceyBranch
import SymmetricSubgroupAsymptotics.TraceyBinaryFiveSixteenths
import SymmetricSubgroupAsymptotics.Non2UnipotentSection
import SymmetricSubgroupAsymptotics.Non2ResidualOrbitCapacity

/-!
# The retained nonbinary section-capacity theorem

This theorem joins the literal annihilator cut, the actual fixed/nonfixed
Schur-row decomposition, and the central-prefix numerical reserve.  Its
remaining structural input is precisely the coupled nonfixed-row estimate
for every actual central quotient, together with the two permutation-section
dimension budgets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {B : Type} [Group B] [Finite B]

/-- The canonical projection to a retained central quotient is an
intertwining map for the unchanged original `B`-action. -/
def non2CentralCutProjection
    (M : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants}) :
    M.ρ.IntertwiningMap
      (OriginalCentralCutExtension.quotientModule M C).ρ where
  toLinearMap := C.1.mkQ
  isIntertwining' := fun _ => rfl

theorem non2CentralCutProjection_surjective
    (M : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants}) :
    Function.Surjective (non2CentralCutProjection M C) :=
  C.1.mkQ_surjective

/-- The actual retained cut satisfies the full `47/48` Schur-capacity
bound and leaves the explicit fusion reserve.  The coupled hypothesis is
about the concrete nonfixed Schur capacity of each literal quotient. -/
theorem exists_non2SectionCapacity_cut
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M] (s : Nat)
    (hs : 24 ≤ s)
    (hfixed : 16 * Module.finrank (ZMod 2) M.ρ.invariants ≤ 5 * s)
    (hunipotent :
      8 * (Module.finrank (ZMod 2) M.ρ.invariants +
        Module.finrank (ZMod 2) (displacementSlice M.ρ M.ρ.invariants)) ≤
          3 * s)
    (hcoupled :
      ∀ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
        Module.finrank (ZMod 2) C.1 = non2CentralCutDimension
          (Module.finrank (ZMod 2) M.ρ.invariants)
          (Module.finrank (ZMod 2)
            (displacementSlice M.ρ M.ρ.invariants)) →
        displacementSlice M.ρ C.1 = ⊥ →
        2 * (Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants : ℝ) +
          4 * representationNonfixedSchurCapacity
            (OriginalCentralCutExtension.quotientModule M C).ρ ≤
              47 * (s : ℝ) / 48) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (s : ℝ) / 48 ∧
      (s : ℝ) / 768 ≤ OriginalCentralCutFusion.gapParameter M C (2 * s) s := by
  let t := Module.finrank (ZMod 2) M.ρ.invariants
  let ell := Module.finrank (ZMod 2)
    (displacementSlice M.ρ M.ρ.invariants)
  obtain ⟨C, hCdim, hCslice, hQdim⟩ :=
    exists_non2RetainedAnnihilatorCut M.ρ
  letI : FiniteDimensional (ZMod 2)
      (OriginalCentralCutExtension.quotientModule M C) :=
    FiniteDimensional.of_surjective C.1.mkQ C.1.mkQ_surjective
  have hQdim' : Module.finrank (ZMod 2)
      (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell := by
    change Module.finrank (ZMod 2)
      (centralQuotientRepresentation M.ρ C.1 C.2).invariants = _
    exact hQdim
  let r := representationNonfixedSchurCapacity
    (OriginalCentralCutExtension.quotientModule M C).ρ
  have hcapacity : OriginalCentralCutFusion.capacity M C ≤
      max (((t - non2CentralCutDimension t ell : Nat) : ℝ)) r := by
    have h := representationSchurCapacity_le_max_fixed_nonfixed
      (OriginalCentralCutExtension.quotientModule M C).ρ
    unfold OriginalCentralCutFusion.capacity
    rw [hQdim'] at h
    exact h
  have hcoupledC :
      2 * (t - non2CentralCutDimension t ell : Nat) + 4 * r ≤
        47 * (s : ℝ) / 48 := by
    have h := hcoupled C hCdim hCslice
    rw [hQdim'] at h
    exact h
  have hcost := OriginalCentralCutFusion.cost_le_of_retained_annihilator
    M C s t ell r hs hfixed hunipotent hCdim hcapacity hcoupledC
  have hgap := OriginalCentralCutFusion.gapParameter_ge_of_cost M C s hcost
  exact ⟨C, hCdim, hCslice, hQdim, hcost, hgap⟩

/-- It is enough to assign every nonfixed simple row of every admissible
retained cut to one of the four checked coupled certificates.  Supremum
passage and the final cut choice are then automatic. -/
theorem exists_non2SectionCapacity_cut_of_certificates
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M] (s : Nat)
    (hs : 24 ≤ s)
    (hfixed : 16 * Module.finrank (ZMod 2) M.ρ.invariants ≤ 5 * s)
    (hunipotent :
      8 * (Module.finrank (ZMod 2) M.ρ.invariants +
        Module.finrank (ZMod 2) (displacementSlice M.ρ M.ρ.invariants)) ≤
          3 * s)
    (hcert :
      ∀ (C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants}),
        Module.finrank (ZMod 2) C.1 = non2CentralCutDimension
          (Module.finrank (ZMod 2) M.ρ.invariants)
          (Module.finrank (ZMod 2)
            (displacementSlice M.ρ M.ρ.invariants)) →
        displacementSlice M.ρ C.1 = ⊥ →
        ∀ (S : Submodule (ZMod 2)[B]
          (OriginalCentralCutExtension.quotientModule M C).ρ.asModule),
          IsSimpleModule (ZMod 2)[B] S →
          (hnonfixed : ¬ representationSubmoduleFixed
            (OriginalCentralCutExtension.quotientModule M C).ρ S) →
          Non2CoupledRowCertificate (s : ℝ)
            (Module.finrank (ZMod 2)
              (OriginalCentralCutExtension.quotientModule M C).ρ.invariants : ℝ)
            ((Module.finrank (ZMod 2)
              (S →ₗ[(ZMod 2)[B]]
                (OriginalCentralCutExtension.quotientModule M C).ρ.asModule) : ℝ) /
              Module.finrank (ZMod 2) S)) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (s : ℝ) / 48 ∧
      (s : ℝ) / 768 ≤ OriginalCentralCutFusion.gapParameter M C (2 * s) s := by
  apply exists_non2SectionCapacity_cut M s hs hfixed hunipotent
  intro C hCdim hCslice
  letI : FiniteDimensional (ZMod 2)
      (OriginalCentralCutExtension.quotientModule M C) :=
    FiniteDimensional.of_surjective C.1.mkQ C.1.mkQ_surjective
  let q := Module.finrank (ZMod 2)
    (OriginalCentralCutExtension.quotientModule M C).ρ.invariants
  have hQdim : q = Module.finrank (ZMod 2) M.ρ.invariants -
      Module.finrank (ZMod 2) C.1 := by
    change Module.finrank (ZMod 2)
      (centralQuotientRepresentation M.ρ C.1 C.2).invariants = _
    exact centralQuotient_invariants_finrank_of_slice_eq_bot
      M.ρ C.1 C.2 hCslice
  have hqle : q ≤ Module.finrank (ZMod 2) M.ρ.invariants := by
    rw [hQdim]
    omega
  have hbase : 2 * (q : ℝ) ≤ 47 * (s : ℝ) / 48 := by
    have hfixedR :
        16 * (Module.finrank (ZMod 2) M.ρ.invariants : ℝ) ≤
          5 * (s : ℝ) := by
      exact_mod_cast hfixed
    have hqleR : (q : ℝ) ≤
        Module.finrank (ZMod 2) M.ρ.invariants := by
      exact_mod_cast hqle
    linarith
  apply representationNonfixedSchurCapacity_coupled_of_certificates
    (OriginalCentralCutExtension.quotientModule M C).ρ (s : ℝ) (q : ℝ)
    (by positivity) hbase
  intro S hS hnonfixed
  exact hcert C hCdim hCslice S hS hnonfixed

/-- The exact Tracey formula and one original faithful transitive
permutation section discharge every nonfixed Schur-row certificate in every
retained central quotient.  The fixed and unipotent budgets remain the two
separate inputs to the final central-cut calculation. -/
theorem exists_non2SectionCapacity_cut_of_Tracey_formula
    {X : Type} [Finite X] [MulAction B X] [FaithfulSMul B X]
    [MulAction.IsPretransitive B X]
    (hTracey : TraceyBinaryFormulaInput) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : P.toRepresentation.IntertwiningMap M.ρ)
    (hqmap : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X))
    (hfixed :
      16 * Module.finrank (ZMod 2) M.ρ.invariants ≤ 5 * Nat.card X)
    (hunipotent :
      8 * (Module.finrank (ZMod 2) M.ρ.invariants +
        Module.finrank (ZMod 2)
          (displacementSlice M.ρ M.ρ.invariants)) ≤ 3 * Nat.card X) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (Nat.card X : ℝ) / 48 ∧
      (Nat.card X : ℝ) / 768 ≤
        OriginalCentralCutFusion.gapParameter M C (2 * Nat.card X)
          (Nat.card X) := by
  apply exists_non2SectionCapacity_cut_of_certificates M (Nat.card X)
    hs hfixed hunipotent
  intro C _ _ S hS hnonfixed
  letI : FiniteDimensional (ZMod 2)
      (OriginalCentralCutExtension.quotientModule M C) :=
    FiniteDimensional.of_surjective C.1.mkQ C.1.mkQ_surjective
  letI : IsSimpleModule (ZMod 2)[B] S := hS
  let qcut := non2CentralCutProjection M C
  have hqcut : Function.Surjective qcut :=
    non2CentralCutProjection_surjective M C
  have hbranch := Non2SchurStructuralBranch.of_Tracey_formula
    hTracey x (OriginalCentralCutExtension.quotientModule M C).ρ S
    hnonfixed P (qcut.comp qmap) (hqcut.comp hqmap) hs heven
  exact hbranch.rowCertificate
    (OriginalCentralCutExtension.quotientModule M C).ρ S
    (Nat.card X)
    (Module.finrank (ZMod 2)
      (OriginalCentralCutExtension.quotientModule M C).ρ.invariants)

/-- Once the unique minimally-transitive `3 * 2^a` literature input is
retained explicitly, the exact Tracey formula also supplies the sharp fixed
budget.  The unipotent-section estimate is then the sole remaining premise
at the complete section-capacity boundary. -/
theorem exists_non2SectionCapacity_cut_of_Tracey_inputs
    {X : Type} [Finite X] [MulAction B X] [FaithfulSMul B X]
    [MulAction.IsPretransitive B X]
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : P.toRepresentation.IntertwiningMap M.ρ)
    (hqmap : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X))
    (hunipotent :
      8 * (Module.finrank (ZMod 2) M.ρ.invariants +
        Module.finrank (ZMod 2)
          (displacementSlice M.ρ M.ρ.invariants)) ≤ 3 * Nat.card X) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (Nat.card X : ℝ) / 48 ∧
      (Nat.card X : ℝ) / 768 ≤
        OriginalCentralCutFusion.gapParameter M C (2 * Nat.card X)
          (Nat.card X) := by
  apply exists_non2SectionCapacity_cut_of_Tracey_formula
    hTracey x M P qmap hqmap hs heven
  · exact binary_permutationSection_invariants_five_sixteenths
      hTracey hExceptional M.ρ P qmap hqmap hs
  · exact hunipotent

/-- Local `3/8` head caps on the literal `O²(B)` orbits now discharge the
last unipotent premise.  This is the complete section-capacity theorem with
only the two named Tracey literature inputs and the residual-orbit caps
visible at its boundary. -/
theorem exists_non2SectionCapacity_cut_of_residual_orbit_caps
    {X : Type} [Finite X] [MulAction B X] [FaithfulSMul B X]
    [MulAction.IsPretransitive B X]
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : P.toRepresentation.IntertwiningMap M.ρ)
    (hqmap : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X))
    (cap : MulAction.orbitRel.Quotient (terminalTwoResidual B) X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient (terminalTwoResidual B) X)
      (S : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2)
          (terminalTwoResidual B) o.orbit)),
      Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (terminalTwoResidual B) (ZMod 2))) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient (terminalTwoResidual B) X,
      8 * cap o ≤ 3 * Nat.card o.orbit) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (Nat.card X : ℝ) / 48 ∧
      (Nat.card X : ℝ) / 768 ≤
        OriginalCentralCutFusion.gapParameter M C (2 * Nat.card X)
          (Nat.card X) := by
  apply exists_non2SectionCapacity_cut_of_Tracey_inputs
    hTracey hExceptional x M P qmap hqmap hs heven
  exact binary_permutationSection_unipotent_of_residual_orbit_caps
    M.ρ P qmap hqmap cap hcap hweight

/-- Complete nonbinary section capacity from the two named Tracey inputs.
The exact two-step preimage and the literal `O²(B)` orbit theorem now derive
the former unipotent premise internally. -/
theorem exists_non2SectionCapacity_cut_of_Tracey_inputs_full
    {X : Type} [Finite X] [MulAction B X] [FaithfulSMul B X]
    [MulAction.IsPretransitive B X]
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hB : ¬IsPGroup 2 B) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : P.toRepresentation.IntertwiningMap M.ρ)
    (hqmap : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X)) :
    let t := Module.finrank (ZMod 2) M.ρ.invariants
    let ell := Module.finrank (ZMod 2)
      (displacementSlice M.ρ M.ρ.invariants)
    ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
      Module.finrank (ZMod 2) C.1 = non2CentralCutDimension t ell ∧
      displacementSlice M.ρ C.1 = ⊥ ∧
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M C).ρ.invariants =
        t - non2CentralCutDimension t ell ∧
      2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
          4 * OriginalCentralCutFusion.capacity M C ≤
        47 * (Nat.card X : ℝ) / 48 ∧
      (Nat.card X : ℝ) / 768 ≤
        OriginalCentralCutFusion.gapParameter M C (2 * Nat.card X)
          (Nat.card X) := by
  apply exists_non2SectionCapacity_cut_of_Tracey_inputs
    hTracey hExceptional x M P qmap hqmap hs heven
  exact binary_permutationSection_unipotent_of_Tracey
    hTracey hB M.ρ P qmap hqmap

end SymmetricSubgroupAsymptotics

end
