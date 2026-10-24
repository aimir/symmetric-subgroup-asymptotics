import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootIntersections
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! The actual retained opposition square lies in D. Consequently it
swaps the two positive/negative minimal families in both directions,
and the SAME original negative intersections have cardinal q and q².
No source-square identity or original automorphism lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOppositionDiagonalResidual
open CFSGReeFFourMinimalParabolics CFSGReeFFourOppositeMinimalParabolics
open CFSGReeFFourOppositeParabolicRootIntersection CFSGReeFFourBorelIntersection
open CFSGReeFFourOriginalMinimalParabolics CFSGReeFFourOriginalRootIntersections
open CFSGReeFFourOriginalBorelNormalizers CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalOppositeAlignment CFSGKernelControlledIntersection
open CFSGOpposedSubgroupPeeling CFSGSubgroupConjugateRestriction

private theorem twice_conj_map {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hgg : g*g∈Subgroup.normalizer (H : Set G)) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom=H := by
  rw [Subgroup.map_map]
  have hf : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom=
      (MulAut.conj (g*g)).toMonoidHom := by
    ext x
    change g*(g*x*g⁻¹)*g⁻¹=(g*g)*x*(g*g)⁻¹
    group
  rw [hf]
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hgg

theorem fixed_negative_image_eq_fixed_positive (m : ℕ) :
    (fixedNegative m).map (MulAut.conj (oppositionFixed m)).toMonoidHom=fixedPositive m := by
  have hn : oppositionFixed m*oppositionFixed m∈
      Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) :=
    (fixedBorel_le_normalizer m) (diagonal_le_borel m (opposition_square_mem_diagonal m))
  have h := twice_conj_map (fixedPositive m) (oppositionFixed m) hn
  rw [fixed_positive_image_eq_fixed_negative] at h
  exact h

theorem negativeSimpleParabolic_opposition_map (m : ℕ) (b : Bool) :
    (negativeSimpleParabolic m b).map (MulAut.conj (oppositionFixed m)).toMonoidHom=
      simpleParabolic m b := by
  have hd : oppositionFixed m*oppositionFixed m∈simpleParabolic m b :=
    (show CFSGReeFFourFixedBorelCardinality.fixedBorel m≤simpleParabolic m b from le_sup_left)
      (diagonal_le_borel m (opposition_square_mem_diagonal m))
  have h := twice_conj_map (simpleParabolic m b) (oppositionFixed m)
    ((simpleParabolic m b).le_normalizer hd)
  rw [simpleParabolic_opposition_map] at h
  exact h

theorem negative_inf_simpleParabolic_eq_opposition_inversion (m : ℕ) (b : Bool) :
    fixedNegative m⊓simpleParabolic m b=
      (inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)).map
        (MulAut.conj (oppositionFixed m)).toMonoidHom := by
  let e : MulAut (originalModelFixed m) := MulAut.conj (oppositionFixed m)
  have hU : (fixedPositive m).map e.toMonoidHom=fixedNegative m :=
    fixed_positive_image_eq_fixed_negative m
  have hP : (negativeSimpleParabolic m b).map e.toMonoidHom=simpleParabolic m b :=
    negativeSimpleParabolic_opposition_map m b
  calc
    _=((fixedPositive m).map e.toMonoidHom)⊓
        ((negativeSimpleParabolic m b).map e.toMonoidHom) :=
      congrArg₂ (fun P Q : Subgroup (originalModelFixed m)=>P⊓Q) hU.symm hP.symm
    _=(fixedPositive m⊓negativeSimpleParabolic m b).map e.toMonoidHom :=
      (Subgroup.map_inf (fixedPositive m) (negativeSimpleParabolic m b) e.toMonoidHom e.injective).symm
    _=_ := congrArg (fun P : Subgroup (originalModelFixed m)=>P.map e.toMonoidHom)
      (positive_inf_negativeSimpleParabolic_eq_inversion m b)

def originalNegativeRootBlock (m : ℕ) (hm : 0<m) (b : Bool) : Subgroup (CFSG.Models.ReeF4 m) :=
  (originalRootBlock m hm b).map
    (MulAut.conj (fixedToOriginal m hm (oppositionFixed m))).toMonoidHom

theorem original_negative_inf_simpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    originalNegative m hm⊓originalSimpleParabolic m hm b=originalNegativeRootBlock m hm b := by
  have hk : (fixedToOriginal m hm).ker≤simpleParabolic m b :=
    (fixedToOriginal_kernel_le_borel m hm).trans le_sup_left
  have h := congrArg (fun P : Subgroup (originalModelFixed m)=>P.map (fixedToOriginal m hm))
    (negative_inf_simpleParabolic_eq_opposition_inversion m b)
  dsimp only at h
  rw [map_inf_eq_of_kernel_le_right (fixedToOriginal m hm) _ _ hk,map_conjugate] at h
  exact h

theorem originalNegativeRootBlock_card (m : ℕ) (hm : 0<m) (b : Bool) :
    Nat.card (originalNegativeRootBlock m hm b)=(2^(2*m+1))^(if b then 2 else 1) := by
  have h := Nat.card_congr ((MulAut.conj (fixedToOriginal m hm (oppositionFixed m))).subgroupMap
    (originalRootBlock m hm b)).toEquiv
  change Nat.card (originalRootBlock m hm b)=Nat.card (originalNegativeRootBlock m hm b) at h
  rw [←h]
  exact originalRootBlock_card m hm b

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections
