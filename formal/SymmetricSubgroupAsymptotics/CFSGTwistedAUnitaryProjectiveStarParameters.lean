import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIntrinsicStarIdentification
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearDiagonal

/-! Literal projective Hermitian coefficients: the original cover is
injective on the whole natural shear subgroup, because every displayed
diagonal entry is one. Thus the original intrinsic root star is
multiplicatively equivalent to the actual additive Hermitian carrier,
with no scalar kernel left unaccounted for. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

theorem starFixed_diagonal (q : CFSG.PrimePower) (s : ℕ) (x : StarParameters q s)
    (k : Fin (s + 4)) :
    ((starFixed q s x).val.val : Mat (q.Extension 2) (s + 3)) k k = 1 := by
  rw [starFixed_matrix]
  exact CFSGTwoPlaneShearArrays.unit_diagonal (starPositive s) (starNegative s)
    (star_coordinates_disjoint s) (starCoefficient q s x) k

theorem projectiveStarParameters_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective ((unitaryProjectiveCover q s).comp (starParameterHom q s)) := by
  intro x y he
  have he' : unitaryProjectiveCover q s (starFixed q s x.toAdd) =
      unitaryProjectiveCover q s (starFixed q s y.toAdd) := he
  obtain ⟨c, hc⟩ := unitaryProjectiveCover_eq_scalar q s _ _ he'
  have h00 := congrArg (fun M : Mat (q.Extension 2) (s + 3) => M 0 0) hc
  change ((starFixed q s x.toAdd).val.val : Mat (q.Extension 2) (s + 3)) 0 0 =
    c * ((starFixed q s y.toAdd).val.val : Mat (q.Extension 2) (s + 3)) 0 0 at h00
  rw [starFixed_diagonal, starFixed_diagonal, mul_one] at h00
  have hx : starFixed q s x.toAdd = starFixed q s y.toAdd := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simpa only [← h00, one_smul] using hc
  exact Multiplicative.toAdd.injective (starFixed_injective q s hx)

def projectiveHermitianStarHom (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    Multiplicative (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) →*
      CFSG.Models.TwistedA (s + 3) q :=
  (unitaryProjectiveCover q s).comp (starHermitianParameterHom q s t ht htc)

theorem projectiveHermitianStarHom_injective (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    Function.Injective (projectiveHermitianStarHom q s t ht htc) := by
  intro A B he
  have h := projectiveStarParameters_injective q s
    (show ((unitaryProjectiveCover q s).comp (starParameterHom q s))
      (Multiplicative.ofAdd ((starHermitianEquiv q s t ht htc).symm A.toAdd)) =
      ((unitaryProjectiveCover q s).comp (starParameterHom q s))
      (Multiplicative.ofAdd ((starHermitianEquiv q s t ht htc).symm B.toAdd)) from he)
  exact Multiplicative.toAdd.injective ((starHermitianEquiv q s t ht htc).symm.injective
    (congrArg Multiplicative.toAdd h))

theorem projectiveHermitianStarHom_range (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    (projectiveHermitianStarHom q s t ht htc).range = unitaryRootStar q s (starPlane q s) := by
  rw [← naturalRootStarGroup_projective_eq_intrinsicStar]
  apply le_antisymm
  · rintro g ⟨A, rfl⟩
    exact ⟨_, ⟨Multiplicative.ofAdd ((starHermitianEquiv q s t ht htc).symm A.toAdd), rfl⟩, rfl⟩
  · rintro g ⟨x, ⟨a, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd ((starHermitianEquiv q s t ht htc) a.toAdd), ?_⟩
    change unitaryProjectiveCover q s (starFixed q s ((starHermitianEquiv q s t ht htc).symm
      ((starHermitianEquiv q s t ht htc) a.toAdd))) = _
    rw [AddEquiv.symm_apply_apply]
    rfl

def projectiveHermitianStarEquiv (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    Multiplicative (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) ≃*
      unitaryRootStar q s (starPlane q s) :=
  (MonoidHom.ofInjective (projectiveHermitianStarHom_injective q s t ht htc)).trans
    (MulEquiv.subgroupCongr (projectiveHermitianStarHom_range q s t ht htc))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
