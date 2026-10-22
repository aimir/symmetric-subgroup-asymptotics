import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAxisAction

/-! Actual ambient original complement subgroups agree with the literal
projection of the canonical complements. Ambient automorphisms preserving
U permute them, and therefore permute their FULL ambient normalizers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAmbient
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateOriginalLeadingAutomorphism
open CFSGNormTwoCoordinateComplementKernel CFSGNormTwoGeckPositiveComplement
open CFSGSimpleCoordinateAxes CFSGSimpleCoordinateHyperplanes

open CFSGNormTwoCoordinateOriginalComplementAction CFSGNormTwoCoordinateOriginalAxisAction
open CFSGInvariantSubgroupCoordinateImage CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckPositivePGroup

def originalComplementAmbient (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  (originalComplement A hd hs hp ho K p i j).map (originalPositive A hd hs hp ho K i).subtype

theorem originalComplementAmbient_eq_projection (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    originalComplementAmbient A hd hs hp ho K p i j=
      ((positiveComplement A hs hp b₀ s₀ K j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (originalProjection A hd hs hp ho K i) := by
  let U := PositiveGroup A hd hs hp ho K
  let H := ElementaryGroup A hd hs hp ho K
  let M := positiveComplement A hs hp b₀ s₀ K j
  have hMU : M≤U := complement_le_positive A hs hp b₀ s₀ K j
  have hjoin : U⊔rootGroup A hs hp b₀ s₀ K true=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hi : (M.subgroupOf U).map (positiveInclusion A hd hs hp ho K)=M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map,Subgroup.map_subgroupOf_eq_of_le (hMU.trans hUH)]
    change (M.subgroupOf U).map U.subtype=M
    exact Subgroup.map_subgroupOf_eq_of_le hMU
  change ((M.subgroupOf U).map (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom).map
    (originalPositive A hd hs hp ho K i).subtype=(M.subgroupOf H).map _
  rw [Subgroup.map_map]
  have hc : (originalPositive A hd hs hp ho K i).subtype.comp
      (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom=
        (originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K) := rfl
  rw [hc,←Subgroup.map_map,hi]

theorem originalComplementAmbient_map (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=originalPositive A hd hs hp ho K i)
    (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom=axis (K:=K) (σ j)) (j : Fin r) :
    (originalComplementAmbient A hd hs hp ho K p i j).map f.toMonoidHom=
      originalComplementAmbient A hd hs hp ho K p i (σ j) := by
  let g := restrictAut (originalPositive A hd hs hp ho K i) f hU
  have hm := originalComplement_map_positiveAut A hd hs hp ho K p i g σ hσ j
  change ((originalComplement A hd hs hp ho K p i j).map
    (originalPositive A hd hs hp ho K i).subtype).map f.toMonoidHom=_
  calc
    _=((originalComplement A hd hs hp ho K p i j).map g.toMonoidHom).map
        (originalPositive A hd hs hp ho K i).subtype := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
    _=originalComplementAmbient A hd hs hp ho K p i (σ j) := by rw [hm];rfl

theorem originalComplementNormalizer_map (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hU : (originalPositive A hd hs hp ho K i).map f.toMonoidHom=originalPositive A hd hs hp ho K i)
    (σ : Equiv.Perm (Fin r))
    (hσ : ∀j : Fin r,(axis (K:=K) j).map
      (ambientLeadingAut A hd hs hp ho K p i f hU).toMonoidHom=axis (K:=K) (σ j)) (j : Fin r) :
    (Subgroup.normalizer (originalComplementAmbient A hd hs hp ho K p i j : Set _)).map f.toMonoidHom=
      Subgroup.normalizer (originalComplementAmbient A hd hs hp ho K p i (σ j) : Set _) := by
  rw [Subgroup.map_equiv_normalizer_eq,originalComplementAmbient_map A hd hs hp ho K p i f hU σ hσ j]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAmbient
