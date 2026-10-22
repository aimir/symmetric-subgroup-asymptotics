import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! All original lattice-labelled root groups, transported through the
SAME originalProjection, are conjugate in the ORIGINAL simple projective
Serre model. For positive roots this agrees with the earlier U-restricted
root line. No faithfulness of the full source or automorphism lift occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateRootOrbitTransitive CFSGNormTwoCoordinateOriginalRootFamily
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGSubgroupConjugateRestriction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def elementaryRootSubgroup (k : Roots A) : Subgroup (ElementaryGroup A hd hs hp ho K) :=
  (rootSubgroup A hd hs hp ho K k).subgroupOf (ElementaryGroup A hd hs hp ho K)

theorem elementaryRootSubgroup_conjugate (k l : Roots A) :
    ∃g : ElementaryGroup A hd hs hp ho K,
      (elementaryRootSubgroup A hd hs hp ho K k).map (MulAut.conj g).toMonoidHom=
        elementaryRootSubgroup A hd hs hp ho K l := by
  obtain ⟨w,hw⟩ := rootSubgroup_conjugate_by_word A hd hs hp ho K k l
  let g := elementaryWord A hd hs hp ho K w
  refine ⟨g,?_⟩
  exact restrict_conjugate (ElementaryGroup A hd hs hp ho K)
    (rootSubgroup A hd hs hp ho K k) (rootSubgroup A hd hs hp ho K l)
    (rootSubgroup_le_elementary A hd hs hp ho K k)
    (rootSubgroup_le_elementary A hd hs hp ho K l) g hw

def originalFullRootLine [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (k : Roots A) : Subgroup (Projective (cartan b₀ s₀) K) :=
  (elementaryRootSubgroup A hd hs hp ho K k).map (originalProjection A hd hs hp ho K i)

theorem originalFullRootLine_conjugate [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (k l : Roots A) :
    ∃g : Projective (cartan b₀ s₀) K,
      (originalFullRootLine A hd hs hp ho K i k).map (MulAut.conj g).toMonoidHom=
        originalFullRootLine A hd hs hp ho K i l := by
  obtain ⟨g,hg⟩ := elementaryRootSubgroup_conjugate A hd hs hp ho K k l
  refine ⟨originalProjection A hd hs hp ho K i g,?_⟩
  change ((elementaryRootSubgroup A hd hs hp ho K k).map (originalProjection A hd hs hp ho K i)).map
    (MulAut.conj (originalProjection A hd hs hp ho K i g)).toMonoidHom=_
  rw [←map_conjugate,hg]
  rfl

theorem originalFullRootLine_eq_positive [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (k : Roots A) (hk : ∀j,0≤k.val j) :
    originalFullRootLine A hd hs hp ho K i k=originalRootLine A hd hs hp ho K i k := by
  have hrest : ((rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)).map
      (positiveInclusion A hd hs hp ho K)=elementaryRootSubgroup A hd hs hp ho K k := by
    apply Subgroup.map_injective (ElementaryGroup A hd hs hp ho K).subtype_injective
    rw [Subgroup.map_map]
    have hc : (ElementaryGroup A hd hs hp ho K).subtype.comp (positiveInclusion A hd hs hp ho K)=
        (PositiveGroup A hd hs hp ho K).subtype := by
      ext x
      rfl
    rw [hc,Subgroup.map_subgroupOf_eq_of_le (positive_root_subgroup_le A hd hs hp ho K k hk)]
    exact (Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_elementary A hd hs hp ho K k)).symm
  change (elementaryRootSubgroup A hd hs hp ho K k).map (originalProjection A hd hs hp ho K i)=
    ((rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)).map
      ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K))
  rw [←Subgroup.map_map,hrest]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines
