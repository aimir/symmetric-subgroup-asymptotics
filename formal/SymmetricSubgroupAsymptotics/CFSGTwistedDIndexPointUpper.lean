import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointAction
import SymmetricSubgroupAsymptotics.CFSGQuotientOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A moved natural point gives a proper subgroup of the SAME original
twisted-D model. Its actual orbit injects into the defining-fixed vector
carrier, yielding the coarse q^(2r) upper bound without a point census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIndexPointUpper
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeCenter
open CFSGProjectiveLinearPointAction CFSGOrthogonalDIndexPointAction
open CFSGTwistedDFixedVectorCardinality CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDRelativeFixedGroup CFSGSerreOrdinaryTwists
open CFSGProjectiveFrameCoordinates PrimitiveSocleRawStructure

abbrev relativePointAction (s : ℕ) (q : CFSG.PrimePower) :
    MulAction (relativeRootGroup (s + 2) q) (NaturalPoints (q.Extension 2) (s + 4)) :=
  MulAction.compHom _ (linearEquiv.toMonoidHom.comp (relativeRootGroup (s + 2) q).subtype)

def firstRelativeRoot (s : ℕ) (q : CFSG.PrimePower) : relativeRootGroup (s + 2) q :=
  ⟨rootTransvection (q.Extension 2) (s + 4) false 0 1,
    CFSGTwistedDRelativeElementaryGroup.chain_mem (s + 2) q false 0 1⟩

theorem center_fixes_point (s : ℕ) (q : CFSG.PrimePower)
    (u : relativeRootGroup (s + 2) q)
    (hu : u ∈ Subgroup.center (relativeRootGroup (s + 2) q))
    (p : NaturalPoints (q.Extension 2) (s + 4)) :
    letI := relativePointAction s q
    u • p = p := by
  letI := relativePointAction s q
  obtain ⟨c, hc⟩ := (relativeRootGroup_center_iff_scalar (s + 2) q u).mp hu
  change linearEquiv u.val • p = p
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' (q.Extension 2) _ _ _ _).mpr
  refine ⟨c, ?_⟩
  change c • p.rep = (u.val : Mat (q.Extension 2) (s + 4)) *ᵥ p.rep
  rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem first_root_moves (s : ℕ) (q : CFSG.PrimePower) :
    letI := relativePointAction s q
    firstRelativeRoot s q • movedPoint (q.Extension 2) s ≠ movedPoint (q.Extension 2) s := by
  letI := relativePointAction s q
  change linearEquiv (firstRelativeRoot s q).val • movedPoint (q.Extension 2) s ≠ _
  exact first_root_moves_point (q.Extension 2) s

abbrev movedOrbit (s : ℕ) (q : CFSG.PrimePower) :=
  letI := relativePointAction s q
  MulAction.orbit (relativeRootGroup (s + 2) q) (movedPoint (q.Extension 2) s)

def orbitRepresentative (s : ℕ) (q : CFSG.PrimePower) (y : movedOrbit s q) :
    relativeRootGroup (s + 2) q := by
  letI := relativePointAction s q
  exact Classical.choose (MulAction.mem_orbit_iff.mp y.property)

theorem orbitRepresentative_point (s : ℕ) (q : CFSG.PrimePower) (y : movedOrbit s q) :
    letI := relativePointAction s q
    orbitRepresentative s q y • movedPoint (q.Extension 2) s = y.val := by
  letI := relativePointAction s q
  exact Classical.choose_spec (MulAction.mem_orbit_iff.mp y.property)

theorem moved_basis_fixed (s : ℕ) (q : CFSG.PrimePower) :
    vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (s + 4))) 1) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (s + 4))) 1 := by
  have hi : (⟨1, by omega⟩ : Fin (s + 4)) ≠ last (s + 2) := by
    intro h
    have he := congrArg Fin.val h
    change 1 = s + 3 at he
    omega
  exact CFSGTwistedDNormalizeFirstPair.fixed_basis _ (s + 2) _ _
    (by rw [CFSGTwistedDNaturalFork.flip_pos, if_neg hi])

def orbitVector (s : ℕ) (q : CFSG.PrimePower) (y : movedOrbit s q) : fixedVectors (s + 2) q :=
  ⟨((orbitRepresentative s q y).val : Mat (q.Extension 2) (s + 4)) *ᵥ
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (s + 4))) 1,
    relative_preserves_fixed_vectors (s + 2) q (orbitRepresentative s q y) _ (moved_basis_fixed s q)⟩

theorem orbitVector_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (orbitVector s q) := by
  letI := relativePointAction s q
  intro y z h
  apply Subtype.ext
  rw [← orbitRepresentative_point s q y, ← orbitRepresentative_point s q z]
  change linearEquiv (orbitRepresentative s q y).val • movedPoint (q.Extension 2) s =
    linearEquiv (orbitRepresentative s q z).val • movedPoint (q.Extension 2) s
  rw [movedPoint, basisPoint, Projectivization.smul_mk, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' (q.Extension 2) _ _ _ _).mpr
  refine ⟨1, ?_⟩
  have he := congrArg (fun v : fixedVectors (s + 2) q => v.val) h
  simpa only [one_smul] using he.symm

theorem relative_leastProperIndex_le (s : ℕ) (q : CFSG.PrimePower) (ell : ℕ)
    (hell : LeastProperIndex
      (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) ell) :
    ell ≤ q.order ^ (2 * (s + 4)) := by
  letI := relativePointAction s q
  let π := QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q))
  obtain ⟨H, hH, hi⟩ := CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point_orbit
    π (QuotientGroup.mk'_surjective _) (movedPoint (q.Extension 2) s)
    (by
      intro u hu
      rw [QuotientGroup.ker_mk'] at hu
      exact center_fixes_point s q u hu _)
    (firstRelativeRoot s q) (first_root_moves s q)
  have hc : Nat.card (movedOrbit s q) ≤ q.order ^ (2 * (s + 4)) :=
    (Nat.card_le_card_of_injective (orbitVector s q) (orbitVector_injective s q)).trans
      (fixedVectors_card_le (s + 2) q)
  exact (hell.2 H hH).trans (hi.le.trans hc)

theorem original_leastProperIndex_le (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD (s + 4) q) ell) :
    ell ≤ q.order ^ (2 * (s + 4)) :=
  relative_leastProperIndex_le s q ell
    (CFSGReduction.leastProperIndex_of_mulEquiv
      (CFSGTwistedDRelativeProjectiveModel.originalRelativeProjectiveEquiv s q) ell hell)

end SymmetricSubgroupAsymptotics.CFSGTwistedDIndexPointUpper
