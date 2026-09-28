import SymmetricSubgroupAsymptotics.Non2RetainedAnnihilatorCut
import SymmetricSubgroupAsymptotics.Non2CentralCutFusion
import SymmetricSubgroupAsymptotics.Non2CoupledSchurNumerics

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

end SymmetricSubgroupAsymptotics

end
