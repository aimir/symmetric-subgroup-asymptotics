import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualComponent
import SymmetricSubgroupAsymptotics.CFSGIndexFromPartialParameterCover

/-! The actual defining-fixed elementary subgroup has relative-root
index at most two. Frame reduction is applied to the inverse element,
so the one-sided coset cover requires no unproved torus normality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedElementaryIndex
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeFixedGroup
open CFSGTwistedDFrameReduction CFSGTwistedDResidualComponent
open CFSGTwistedDResidualDiagonal CFSGTwistedDNormOneTorusIndex CFSGTwistedDNormOneUnits

def fixedElementaryUnits (n : ℕ) (q : CFSG.PrimePower) :
    Subgroup ((Mat (q.Extension 2) (n + 2))ˣ) :=
  elementaryRootGroup (q.Extension 2) (n + 2) ⊓ naturalFixedUnits n q

theorem relative_le_fixedElementary (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q ≤ fixedElementaryUnits n q :=
  le_inf (relativeRootGroup_le_elementary n q) (relativeRootGroup_le_fixed n q)

theorem exists_relative_diagonal (s : ℕ) (q : CFSG.PrimePower)
    (u : (Mat (q.Extension 2) (s + 4))ˣ) (hu : u ∈ fixedElementaryUnits (s + 2) q) :
    ∃ a : relativeRootGroup (s + 2) q, ∃ c : normOneUnits q,
      a.val * u = residualDiagonalHom (s + 2) q c := by
  have hQ : u ∈ quadraticPreserving (q.Extension 2) (s + 4) :=
    CFSGOrthogonalDAllRankQuadraticPreservation.elementary_le_quadratic
      (q.Extension 2) (s + 2) hu.1
  obtain ⟨a, b, hab, hbt⟩ := exists_residual (s + 2) q u hQ hu.2
  have he : residualEmbedding (q.Extension 2) (s + 2) b.val ∈
      elementaryRootGroup (q.Extension 2) (s + 4) := by
    rw [← hab]
    exact (elementaryRootGroup (q.Extension 2) (s + 4)).mul_mem
      (relativeRootGroup_le_elementary (s + 2) q a.property) hu.1
  obtain ⟨c, hc⟩ := exists_residual_diagonal s q b hbt he
  refine ⟨a, c, ?_⟩
  rw [hc, residualEmbedding_diagonal] at hab
  exact hab

theorem inverse_diagonal_coset_cover (s : ℕ) (q : CFSG.PrimePower)
    (u : (Mat (q.Extension 2) (s + 4))ˣ) (hu : u ∈ fixedElementaryUnits (s + 2) q) :
    ∃ c : normOneUnits q,
      (residualDiagonalHom (s + 2) q c)⁻¹ * u ∈ relativeRootGroup (s + 2) q := by
  obtain ⟨a, c, hc⟩ := exists_relative_diagonal s q u⁻¹
    ((fixedElementaryUnits (s + 2) q).inv_mem hu)
  refine ⟨c⁻¹, ?_⟩
  rw [map_inv, inv_inv]
  have h : residualDiagonalHom (s + 2) q c * u = a.val := by
    rw [← hc, mul_assoc, inv_mul_cancel, mul_one]
  rw [h]
  exact a.property

theorem relative_index_le_two (s : ℕ) (q : CFSG.PrimePower) :
    ((relativeRootGroup (s + 2) q).subgroupOf (fixedElementaryUnits (s + 2) q)).index ≤ 2 := by
  exact (CFSGIndexFromPartialParameterCover.index_le_of_partial_parameter_cover
    (relativeRootGroup (s + 2) q) (fixedElementaryUnits (s + 2) q)
    (relative_le_fixedElementary (s + 2) q) (residualDiagonalHom (s + 2) q)
    (retainedResidual q) (retained_residual_diagonal_mem (s + 2) q)
    (inverse_diagonal_coset_cover s q)).trans (retainedResidual_index_le_two q)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedElementaryIndex
