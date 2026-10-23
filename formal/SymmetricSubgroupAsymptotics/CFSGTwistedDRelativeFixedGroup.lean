import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorAction

/-! The natural relative-root subgroup is genuinely fixed by the
diagram--field involution, already in rank two. Fixedness of the paired
word uses actual all-sign terminal commutation, not a presumed fixed
group presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDNaturalFieldTwist
open CFSGTwistedDNaturalFork CFSGSerreOrdinaryTwists CFSGTwistedDSingularPrefix
open CFSGTwistedDNaturalQuadraticTwist

def naturalFixedUnits (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup ((Mat (q.Extension 2) (s + 2))ˣ) where
  carrier := {u | unitTwist (q.Extension 2) s (definingFieldAutomorphism q 2) u = u}
  one_mem' := map_one _
  mul_mem' := by
    intro g h hg hh
    change unitTwist (q.Extension 2) s (definingFieldAutomorphism q 2) (g * h) = g * h
    rw [map_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change unitTwist (q.Extension 2) s (definingFieldAutomorphism q 2) g⁻¹ = g⁻¹
    rw [map_inv, hg]

theorem chainNode_fixed (s : ℕ) (i : Fin s) :
    CFSG.Models.dTwist (chainNode s i) = chainNode s i := by
  have hi := i.isLt
  have h2 : 2 ≤ s + 2 := by omega
  have ha : (chainNode s i).val ≠ (s + 2) - 2 := by dsimp only [chainNode]; omega
  have hb : (chainNode s i).val ≠ (s + 2) - 1 := by dsimp only [chainNode]; omega
  simp only [CFSG.Models.dTwist, dif_pos h2, if_neg ha, if_neg hb]

theorem pairedRoot_fixed (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    unitTwist (q.Extension 2) s (definingFieldAutomorphism q 2) (pairedRoot s q neg a) =
      pairedRoot s q neg a := by
  have hσ : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a := by
    simpa only [definingFieldAutomorphism_apply] using
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  rw [pairedRoot, map_mul, unitTwist_root, unitTwist_root, twist_pen, twist_last, hσ]
  exact (CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute
    (q.Extension 2) s neg neg a (definingFieldAutomorphism q 2 a)).eq.symm

theorem relativeRootGroup_le_fixed (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup s q ≤ naturalFixedUnits s q := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨neg, i, a, rfl⟩ | ⟨neg, a, rfl⟩
  · change unitTwist (q.Extension 2) s (definingFieldAutomorphism q 2)
      (rootTransvection (q.Extension 2) (s + 2) neg (chainNode s i) (a : q.Extension 2)) = _
    have ha : definingFieldAutomorphism q 2 (a : q.Extension 2) = (a : q.Extension 2) := a.property
    rw [unitTwist_root, chainNode_fixed, ha]
  · exact pairedRoot_fixed s q neg a

theorem relative_preserves_fixed_vectors (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup s q) (v : Index (s + 2) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) s (definingFieldAutomorphism q 2) v = v) :
    vectorTwist (q.Extension 2) s (definingFieldAutomorphism q 2)
      ((g.val : Mat (q.Extension 2) (s + 2)) *ᵥ v) =
        (g.val : Mat (q.Extension 2) (s + 2)) *ᵥ v := by
  have hg := relativeRootGroup_le_fixed s q g.property
  have hm := congrArg (fun u : (Mat (q.Extension 2) (s + 2))ˣ =>
    (u : Mat (q.Extension 2) (s + 2))) hg
  exact CFSGTwistedDFixedVectorAction.fixed_matrix_preserves_fixed_vectors
    (q.Extension 2) s (definingFieldAutomorphism q 2) _ hm v hv

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
