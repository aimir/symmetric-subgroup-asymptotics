import SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPolarSimilitude
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGlobalField
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularSubspaceAction

/-! Whole semilinear polar realization on the SAME original D quadratic
space. Every original projective-group automorphism in rank at least five
has a coordinate field component and a genuine quadratic similitude.
All incidence, global field coherence and linear gluing are discharged
internally. The quantitative Out bound is a separate consumer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSemilinearPolarSimilitude
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDFieldGeometry
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

theorem exists_field_similitude_decomposition (s : ℕ)
    (f : Points (splitQuadraticForm K (s+4))≃Points (splitQuadraticForm K (s+4)))
    (l : Planes (splitQuadraticForm K (s+4))≃Planes (splitQuadraticForm K (s+4)))
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P R,ZeroOn (splitQuadraticForm K (s+4)).polarBilin (f P).val (f R).val ↔
      ZeroOn (splitQuadraticForm K (s+4)).polarBilin P.val R.val) :
    ∃(σ : K≃+*K) (c : K) (L : (Index (s+4)→K)≃ₗ[K](Index (s+4)→K)),c≠0 ∧
      (∀v,splitQuadraticForm K (s+4) (L v)=c*splitQuadraticForm K (s+4) v) ∧
      ∀R : Points (splitQuadraticForm K (s+4)),
        (normalizedPoints (s+4) f σ R).val=R.val.map L.toLinearMap := by
  obtain ⟨σ,hlinear⟩ := CFSGOrthogonalDGlobalField.exists_linear_normalization K s f l hinc
  obtain ⟨c,L,hc,hQ,hL⟩ := CFSGOrthogonalDLinearPolarSimilitude.exists_similitude K (s+1)
    (normalizedPoints (s+4) f σ) (normalized_orthogonality (s+4) f horth σ) hlinear
  exact ⟨σ,c,L,hc,hQ,hL⟩

theorem original_field_similitude_decomposition (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (F : MulAut (elementaryProjective K (s+5))) :
    ∃(σ : K≃+*K) (c : K) (L : (Index (s+5)→K)≃ₗ[K](Index (s+5)→K)),c≠0 ∧
      (∀v,splitQuadraticForm K (s+5) (L v)=c*splitQuadraticForm K (s+5) v) ∧
      ∀R : Points (splitQuadraticForm K (s+5)),
        (normalizedPoints (s+5) (originalPointPermutationHom K p s F) σ R).val=
          R.val.map L.toLinearMap :=
  exists_field_similitude_decomposition K (s+1) (originalPointPermutationHom K p s F)
    (singularActionHom K p (s+1) F) (originalPointAction_incidence K p s F)
    (originalPointAction_preserves_orthogonal K p s F)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSemilinearPolarSimilitude
