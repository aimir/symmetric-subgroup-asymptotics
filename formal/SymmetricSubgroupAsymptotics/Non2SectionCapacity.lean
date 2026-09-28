import SymmetricSubgroupAsymptotics.Non2RetainedAnnihilatorCut
import SymmetricSubgroupAsymptotics.Non2CentralCutFusion
import SymmetricSubgroupAsymptotics.RepresentationSchurRows

/-!
# The retained nonbinary section-capacity theorem

This theorem joins the literal annihilator cut, the actual fixed/nonfixed
Schur-row decomposition, and the central-prefix numerical reserve.  Its
remaining structural input is precisely the coupled nonfixed-row estimate
for every actual central quotient, together with the two permutation-section
dimension budgets.
-/

set_option autoImplicit false
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
    have h := hcoupled C
    rw [hQdim'] at h
    exact h
  have hcost := OriginalCentralCutFusion.cost_le_of_retained_annihilator
    M C s t ell r hs hfixed hunipotent hCdim hcapacity hcoupledC
  have hgap := OriginalCentralCutFusion.gapParameter_ge_of_cost M C s hcost
  exact ⟨C, hCdim, hCslice, hQdim, hcost, hgap⟩

end SymmetricSubgroupAsymptotics

end
