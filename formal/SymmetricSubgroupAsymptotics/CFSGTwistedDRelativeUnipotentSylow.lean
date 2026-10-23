import SymmetricSubgroupAsymptotics.CFSGTwistedDTestNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagPowerDiagonal
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! The literal relative-root intersection with the standard ambient
unipotent group is an actual defining-characteristic Sylow subgroup.
The checked singular-prefix tests force its normalizer triangular;
Frobenius then kills all diagonal entries of a p-overgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentSylow
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeSignedGroups
open CFSGTwistedDPartialFlagGeometry CFSGTwistedDSingularPrefix
open CFSGOrthogonalDPositiveSimpleUnipotent CFSGOrthogonalDGenerationForkTorus

def relativeInclusion (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup (s + 2) q →* elementaryRootGroup (q.Extension 2) (s + 4) :=
  Subgroup.inclusion (relativeRootGroup_le_elementary (s + 2) q)

theorem relativeInclusion_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (relativeInclusion s q) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : elementaryRootGroup (q.Extension 2) (s + 4) => z.val) h

def unipotent (s : ℕ) (q : CFSG.PrimePower) : Subgroup (relativeRootGroup (s + 2) q) :=
  (CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4)).comap (relativeInclusion s q)

theorem unipotent_isPGroup (s : ℕ) (q : CFSG.PrimePower) :
    IsPGroup q.prime (unipotent s q) :=
  (CFSGOrthogonalDIndexUnipotent.unipotent_isPGroup (q.Extension 2) (s + 4) q.prime).comap_of_injective
    (relativeInclusion s q) (relativeInclusion_injective s q)

theorem tests_mem_image (s : ℕ) (q : CFSG.PrimePower)
    (i : Fin (s + 2) ⊕ Unit) :
    testRoot (q.Extension 2) s i ∈ (unipotent s q).map (relativeInclusion s q) := by
  cases i with
  | inl j =>
    let r : relativeRootGroup (s + 2) q :=
      ⟨rootTransvection (q.Extension 2) (s + 4) false (chainNode (s + 2) j) 1,
        chain_mem (s + 2) q false j 1⟩
    refine ⟨r, ?_, rfl⟩
    exact positive_mem_unipotent (q.Extension 2) (s + 4) _ _
  | inr j =>
    let r : relativeRootGroup (s + 2) q :=
      ⟨pairedRoot (s + 2) q false 1, paired_mem (s + 2) q false 1⟩
    have hr : r ∈ unipotent s q := by
      change pairedRoot (s + 2) q false 1 ∈
        CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (s + 4))
      unfold pairedRoot
      exact (CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (s + 4))).mul_mem
        (positive_mem_unipotent (q.Extension 2) (s + 4) _ _)
        (positive_mem_unipotent (q.Extension 2) (s + 4) _ _)
    refine ⟨r, hr, ?_⟩
    apply Subtype.ext
    change rootTransvection (q.Extension 2) (s + 4) false (pen (s + 2)) 1 *
      rootTransvection (q.Extension 2) (s + 4) false (last (s + 2))
        (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 1) = _
    rw [map_one]
    rfl

theorem normalizer_triangular (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q)
    (hg : g ∈ Subgroup.normalizer (unipotent s q : Set (relativeRootGroup (s + 2) q))) :
    (g.val : Mat (q.Extension 2) (s + 4)).BlockTriangular (flagEquiv (s + 4)) := by
  let P := (unipotent s q).map (relativeInclusion s q)
  have hP : IsPGroup q.prime P := (unipotent_isPGroup s q).map (relativeInclusion s q)
  have hn : relativeInclusion s q g ∈ Subgroup.normalizer
      (P : Set (elementaryRootGroup (q.Extension 2) (s + 4))) :=
    (unipotent s q).le_normalizer_map (relativeInclusion s q) ⟨g, hg, rfl⟩
  exact CFSGTwistedDTestNormalizer.normalizer_triangular (q.Extension 2) s q.prime P hP
    (tests_mem_image s q) (relativeInclusion s q g) hn

theorem pSubgroup_normalizer_le_unipotent (s : ℕ) (q : CFSG.PrimePower)
    (P : Subgroup (relativeRootGroup (s + 2) q)) (hP : IsPGroup q.prime P)
    (hPN : P ≤ Subgroup.normalizer
      (unipotent s q : Set (relativeRootGroup (s + 2) q))) : P ≤ unipotent s q := by
  intro g hg
  have htri := normalizer_triangular s q g (hPN hg)
  refine ⟨htri, ?_⟩
  intro i
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hpow : (g.val : Mat (q.Extension 2) (s + 4)) ^ (q.prime ^ k) = 1 :=
    congrArg (fun x : P => (x.val.val : Mat (q.Extension 2) (s + 4))) hk
  exact CFSGMatrixFlagSubgroups.diagonal_one_of_prime_power (flagEquiv (s + 4))
    q.prime (g.val : Mat (q.Extension 2) (s + 4)) htri k hpow i

def unipotentSylow (s : ℕ) (q : CFSG.PrimePower) : Sylow q.prime (relativeRootGroup (s + 2) q) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (unipotent s q) (unipotent_isPGroup s q)
    (pSubgroup_normalizer_le_unipotent s q)

theorem unipotentSylow_coe (s : ℕ) (q : CFSG.PrimePower) :
    (unipotentSylow s q : Subgroup (relativeRootGroup (s + 2) q)) = unipotent s q := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentSylow
