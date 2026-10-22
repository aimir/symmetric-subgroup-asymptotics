import SymmetricSubgroupAsymptotics.CFSGTwistedAEndpointFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFixedRadicalGroup

/-! Genuine endpoint-paired units and a paired Weyl word in the actual
natural defining-fixed group. The endpoint commutation is proved on the
literal matrices; the same word maps to the ORIGINAL fixed source. This
prepares pair-swap transport, without asserting its support conclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreSquareZeroMatrix CFSGSerreOrdinaryTwists

theorem naturalRootUnit_commute_of_zero {K : Type} [Field K] (r : ℕ)
    (neg : Bool) (i j : Fin r) (a b : K)
    (hij : rootMatrix K r neg i * rootMatrix K r neg j = 0)
    (hji : rootMatrix K r neg j * rootMatrix K r neg i = 0) :
    Commute (naturalRootUnit K r neg i a) (naturalRootUnit K r neg j b) := by
  apply Units.ext
  change (1 + a • rootMatrix K r neg i) * (1 + b • rootMatrix K r neg j) =
    (1 + b • rootMatrix K r neg j) * (1 + a • rootMatrix K r neg i)
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, hij, hji, smul_zero]
  abel

theorem endpoint_rootMatrix_mul_zero (K : Type) [Field K] (s : ℕ) (neg : Bool) :
    rootMatrix K (s + 3) neg (endpointNode s) *
      rootMatrix K (s + 3) neg (endpointNode s).rev = 0 ∧
    rootMatrix K (s + 3) neg (endpointNode s).rev *
      rootMatrix K (s + 3) neg (endpointNode s) = 0 := by
  have h1 : (endpointNode s).succ ≠ (endpointNode s).rev.castSucc := by
    intro h
    have hv := congrArg (fun i : Fin (s + 4) => i.val) h
    simp only [endpointNode, Fin.val_succ, Fin.val_castSucc, Fin.val_rev] at hv
    omega
  have h2 : (endpointNode s).rev.succ ≠ (endpointNode s).castSucc := by
    intro h
    have hv := congrArg (fun i : Fin (s + 4) => i.val) h
    simp only [endpointNode, Fin.val_succ, Fin.val_castSucc, Fin.val_rev] at hv
    omega
  have hp : positive K (s + 3) (endpointNode s) *
      positive K (s + 3) (endpointNode s).rev = 0 := by
    exact Matrix.single_mul_single_of_ne (1 : K) (endpointNode s).castSucc
      (endpointNode s).succ (endpointNode s).rev.castSucc h1 (1 : K)
  have hq : positive K (s + 3) (endpointNode s).rev *
      positive K (s + 3) (endpointNode s) = 0 := by
    exact Matrix.single_mul_single_of_ne (1 : K) (endpointNode s).rev.castSucc
      (endpointNode s).rev.succ (endpointNode s).castSucc h2 (1 : K)
  cases neg
  · exact ⟨hp, hq⟩
  · constructor
    · change (positive K (s + 3) (endpointNode s)).transpose *
        (positive K (s + 3) (endpointNode s).rev).transpose = 0
      rw [← Matrix.transpose_mul, hq, Matrix.transpose_zero]
    · change (positive K (s + 3) (endpointNode s).rev).transpose *
        (positive K (s + 3) (endpointNode s)).transpose = 0
      rw [← Matrix.transpose_mul, hp, Matrix.transpose_zero]

def endpointNaturalFixedPair (q : CFSG.PrimePower) (s : ℕ) (neg : Bool) (t : q.Extension 2) :
    naturalFixed (s + 3) q :=
  ⟨elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) (s + 3)) neg (endpointNode s) t *
    elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) (s + 3)) neg
      (endpointNode s).rev (definingFieldAutomorphism q 2 t), by
    change diagramFieldUnitHom (q.Extension 2) (s + 3) (definingFieldAutomorphism q 2).toRingHom
      (naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s) t *
        naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s).rev
          (definingFieldAutomorphism q 2 t)) = _
    rw [map_mul, CFSGTwistedA2UnitRootTwist.simpleUnit_twist,
      CFSGTwistedA2UnitRootTwist.simpleUnit_twist, Fin.rev_rev]
    have ht : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 t) = t :=
      extension_two_pow_twice q t
    rw [ht]
    obtain ⟨hp, hn⟩ := endpoint_rootMatrix_mul_zero (q.Extension 2) s neg
    exact (naturalRootUnit_commute_of_zero (s + 3) neg (endpointNode s) (endpointNode s).rev
      t (definingFieldAutomorphism q 2 t) hp hn).eq.symm⟩

def endpointPairWeyl (q : CFSG.PrimePower) (s : ℕ) : naturalFixed (s + 3) q :=
  endpointNaturalFixedPair q s false (-1) * endpointNaturalFixedPair q s true 1 *
    endpointNaturalFixedPair q s false (-1)

def originalEndpointPairWeyl (q : CFSG.PrimePower) (s : ℕ) : Fixed (s + 3) q :=
  naturalFixedToOriginal q (s + 3) (endpointPairWeyl q s)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
