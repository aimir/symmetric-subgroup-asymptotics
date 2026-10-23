import SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveHighestShape
import SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveCommutant
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors

/-! Central elements of the SAME relative Sylow have the highest-root
matrix shape, with parameter in the actual fixed field. This proves a
necessary shape; reverse membership is a separate literal-root word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenterShape
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeSignedGroups CFSGTwistedDRelativeUnipotentSylow
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedA2FixedField
open CFSGSerreOrdinaryTwists CFSGTwistedDRelativeFixedGroup

theorem positive_le_relative (n : ℕ) (q : CFSG.PrimePower) :
    signedRootGroup n q false ≤ relativeRootGroup n q := by
  rw [← positive_sup_negative]
  exact le_sup_left

def positiveInU (s : ℕ) (q : CFSG.PrimePower)
    (u : signedRootGroup (s + 2) q false) : unipotent s q :=
  ⟨⟨u.val, positive_le_relative (s + 2) q u.property⟩,
    positive_le_upper_units (s + 2) q u.property⟩

theorem central_positive_commutation (s : ℕ) (q : CFSG.PrimePower)
    (z : unipotent s q) (hz : z ∈ Subgroup.center (unipotent s q))
    (u : (Mat (q.Extension 2) (s + 4))ˣ)
    (hu : u ∈ signedRootGroup (s + 2) q false) :
    (z.val.val : Mat (q.Extension 2) (s + 4)) * (u : Mat (q.Extension 2) (s + 4)) =
      (u : Mat (q.Extension 2) (s + 4)) * (z.val.val : Mat (q.Extension 2) (s + 4)) := by
  have h := (Subgroup.mem_center_iff.mp hz (positiveInU s q ⟨u, hu⟩)).symm
  exact congrArg (fun v : unipotent s q => (v.val.val : Mat (q.Extension 2) (s + 4))) h

theorem central_highest_shape (s : ℕ) (q : CFSG.PrimePower)
    (z : unipotent s q) (hz : z ∈ Subgroup.center (unipotent s q)) :
    ∃ a : q.Extension 2, (z.val.val : Mat (q.Extension 2) (s + 4)) =
      plusArray (0 : Fin (s + 4)) (secondIndex s) a := by
  let za : CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4) :=
    ⟨relativeInclusion s q z.val, z.property⟩
  have hA := CFSGTwistedDPositiveCommutant.positive_directions (s + 2) q
    (z.val.val : Mat (q.Extension 2) (s + 4)) (central_positive_commutation s q z hz)
  exact CFSGTwistedDPositiveHighestShape.highest_shape (q.Extension 2) s za hA

theorem highest_parameter_fixed (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (a : q.Extension 2)
    (hg : (g.val : Mat (q.Extension 2) (s + 4)) =
      plusArray (0 : Fin (s + 4)) (secondIndex s) a) :
    definingFieldAutomorphism q 2 a = a := by
  have h0 : (0 : Fin (s + 4)) ≠ last (s + 2) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = s + 3 at hv
    omega
  have h1 : secondIndex s ≠ last (s + 2) := by
    intro h
    have hv := congrArg Fin.val h
    change 1 = s + 3 at hv
    omega
  let v : Index (s + 4) → q.Extension 2 := Pi.single (Sum.inr (secondIndex s)) 1
  have hv := CFSGTwistedDNormalizeFirstPair.fixed_basis (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2) (Sum.inr (secondIndex s))
    (by rw [CFSGTwistedDNaturalFork.flip_neg, if_neg h1])
  have hw := relative_preserves_fixed_vectors (s + 2) q g v hv
  have ha := CFSGTwistedDFixedVectorCoordinates.positive_fixed (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2) _ hw 0 h0
  have he : ((g.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inl 0) = a := by
    rw [hg]
    simp [v, Matrix.mulVec_single_one, Matrix.col_apply, plusArray,
      Matrix.one_apply, Matrix.single_apply, zero_ne_second, Ne.symm (zero_ne_second s)]
  rw [he] at ha
  exact ha

theorem central_highest_fixed_shape (s : ℕ) (q : CFSG.PrimePower)
    (z : unipotent s q) (hz : z ∈ Subgroup.center (unipotent s q)) :
    ∃ a : fixedField q, (z.val.val : Mat (q.Extension 2) (s + 4)) =
      plusArray (0 : Fin (s + 4)) (secondIndex s) (a : q.Extension 2) := by
  obtain ⟨a, ha⟩ := central_highest_shape s q z hz
  exact ⟨⟨a, highest_parameter_fixed s q z.val a ha⟩, ha⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenterShape
