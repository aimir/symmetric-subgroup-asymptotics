import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedCentralCocycle
import SymmetricSubgroupAsymptotics.CFSGTwistedDForkPositiveAction

/-! Actual natural images of the ORIGINAL paired fixed-root words.
These give literal test-word membership in the SAME fixed-image preimage;
original derived-image membership is deliberately not inferred here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDFixedA2 CFSGTwistedDPairedFixedRoots
open CFSGTwistedDFixedCentralCocycle

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def naturalRoot (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin (s + 4))
    (t : q.Extension 2) : elementaryRootGroup (q.Extension 2) (s + 4) :=
  ⟨rootTransvection (q.Extension 2) (s + 4) neg i t,
    rootTransvection_mem (q.Extension 2) (s + 4) neg i t⟩

def pairedNaturalRoot (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    elementaryRootGroup (q.Extension 2) (s + 4) :=
  naturalRoot s q neg (pen (s + 2)) t * naturalRoot s q neg (last (s + 2)) (t ^ q.order)

theorem root_image (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (i : Fin (s + 4))
    (t : q.Extension 2) :
    orthogonalImageRepresentation (q.Extension 2) (s + 4) (rank_ge_four s)
      (modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg i t) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s) (naturalRoot s q neg i t) :=
  CFSGSerreSquareZeroMatrix.source_root_action_eq_elementary
    (realizationData (s + 4) (rank_ge_four s)) (q.Extension 2)
    (rootTransvection (q.Extension 2) (s + 4))
    (rootTransvection_val_data (q.Extension 2) (s + 4) (rank_ge_four s))
    (rootTransvection_inv_val_data (q.Extension 2) (s + 4) (rank_ge_four s)) neg i t

theorem paired_image (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    fixedImageAction s q (pairedFork s q neg t) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s) (pairedNaturalRoot s q neg t) := by
  let ρ := orthogonalImageRepresentation (q.Extension 2) (s + 4) (rank_ge_four s)
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  change ρ (toModel s q (pairedFork s q neg t)) = ν (pairedNaturalRoot s q neg t)
  rw [pairedFork_toModel]
  calc
    _ = ρ (modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (pen (s + 2)) t) *
        ρ (modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (last (s + 2)) (t ^ q.order)) :=
      ρ.map_mul _ _
    _ = ν (naturalRoot s q neg (pen (s + 2)) t) *
        ν (naturalRoot s q neg (last (s + 2)) (t ^ q.order)) :=
      congrArg₂ (fun a b => a * b) (root_image s q neg (pen (s + 2)) t)
        (root_image s q neg (last (s + 2)) (t ^ q.order))
    _ = _ := (ν.map_mul _ _).symm

theorem paired_mem_preimage (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :
    pairedNaturalRoot s q neg t ∈ naturalFixedPreimage s q :=
  ⟨pairedFork s q neg t, paired_image s q neg t⟩

theorem paired_one_val (s : ℕ) (q : CFSG.PrimePower) :
    (pairedNaturalRoot s q false 1).val =
      CFSGTwistedDForkPositiveAction.foldedFork (q.Extension 2) (s + 2) := by
  change rootTransvection (q.Extension 2) (s + 4) false (pen (s + 2)) 1 *
    rootTransvection (q.Extension 2) (s + 4) false (last (s + 2)) (1 ^ q.order) = _
  rw [one_pow]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
