import SymmetricSubgroupAsymptotics.CFSGFinitePermutationEncoding
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSemilinearPolarSimilitude
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearSimilitudeCoordinates

/-! A faithful family of permutations of the actual quadratic D points
and planes is bounded by the actual GO point image and the field factor.
This applies already in rank four and does not require a full-group
automorphism action on points. It therefore supports point-type subgroups.
The geometric hypotheses are exactly literal incidence and orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPolarFamilyCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDFieldGeometry
open CFSGOrthogonalDSemilinearPolarSimilitude CFSGOrthogonalDProjectiveSimilitudes
open CFSGOrthogonalDLinearSimilitudeCoordinates CFSGOrthogonalDIndexQuadraticForm
open CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K] (s : ℕ)

theorem point_family_card_le_pointImage_mul_field {A : Type*}
    (points : A → Equiv.Perm (Points (splitQuadraticForm K (s+4))))
    (planes : A → Equiv.Perm (Planes (splitQuadraticForm K (s+4))))
    (faithful : Function.Injective points)
    (incidence : ∀a P L,(points a P).val ≤ (planes a L).val ↔ P.val ≤ L.val)
    (orthogonality : ∀a P R,
      ZeroOn (splitQuadraticForm K (s+4)).polarBilin (points a P).val (points a R).val ↔
        ZeroOn (splitQuadraticForm K (s+4)).polarBilin P.val R.val) :
    Nat.card A ≤ Nat.card (pointHom K (s+4)).range * Nat.card (K ≃+* K) := by
  classical
  letI : Finite (K ≃+* K) := Finite.of_injective
    (fun τ : K ≃+* K => (τ : K → K)) DFunLike.coe_injective
  have hd : ∀a, ∃(σ : K ≃+* K) (R : (pointHom K (s+4)).range),
      ∀x,pointEquiv σ.symm (s+4) (points a x)=R.val x := by
    intro a
    obtain ⟨σ,c,L,hc,hQ,hL⟩ := exists_field_similitude_decomposition K s
      (points a) (planes a) (incidence a) (orthogonality a)
    let g := ofLinearEquiv K (s+4) L c hc hQ
    refine ⟨σ,⟨pointHom K (s+4) g,⟨g,rfl⟩⟩,?_⟩
    have he : normalizedPoints (s+4) (points a) σ=pointHom K (s+4) g := by
      rw [ofLinearEquiv_point]
      apply Equiv.ext
      intro R
      apply Subtype.ext
      exact hL R
    exact fun x => congrArg (fun e => e x) he
  have h := CFSGFinitePermutationEncoding.card_le_normalization_mul_realization
    points faithful (fun σ : K ≃+* K => pointEquiv σ.symm (s+4))
    (fun R : (pointHom K (s+4)).range => R.val) hd
  simpa only [mul_comm] using h

theorem point_family_card_le_quadratic_mul_field {A : Type*}
    (points : A → Equiv.Perm (Points (splitQuadraticForm K (s+4))))
    (planes : A → Equiv.Perm (Planes (splitQuadraticForm K (s+4))))
    (faithful : Function.Injective points)
    (incidence : ∀a P L,(points a P).val ≤ (planes a L).val ↔ P.val ≤ L.val)
    (orthogonality : ∀a P R,
      ZeroOn (splitQuadraticForm K (s+4)).polarBilin (points a P).val (points a R).val ↔
        ZeroOn (splitQuadraticForm K (s+4)).polarBilin P.val R.val) :
    Nat.card A ≤ Nat.card (quadraticPreserving K (s+4)) * Nat.card (K ≃+* K) :=
  (point_family_card_le_pointImage_mul_field K s points planes faithful incidence orthogonality).trans
    (Nat.mul_le_mul_right _ (pointImage_card_le_quadratic K (s+4) (by omega)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPolarFamilyCardinality
