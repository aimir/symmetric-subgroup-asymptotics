import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! Intrinsic intersections in the SAME original Ree quotient recover
the actual q and q² positive inversion blocks. Kernel containment controls
the intersection image; injectivity is used only on the proved positive
subgroup to retain the block cardinalities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootIntersections
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourOriginalOppositeAlignment CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourMinimalParabolics CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourOppositeParabolicRootIntersection CFSGReeFFourOriginalMinimalParabolics
open CFSGOpposedSubgroupPeeling CFSGKernelControlledIntersection

def originalRootBlock (m : ℕ) (hm : 0<m) (b : Bool) : Subgroup (CFSG.Models.ReeF4 m) :=
  (inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)).map
    (fixedToOriginal m hm)

theorem original_kernel_le_negativeSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    (fixedToOriginal m hm).ker≤negativeSimpleParabolic m b :=
  (fixedToOriginal_kernel_le_oppositeBorel m hm).trans le_sup_left

theorem original_positive_inf_negativeSimpleParabolic (m : ℕ) (hm : 0<m) (b : Bool) :
    (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m))⊓
      originalNegativeSimpleParabolic m hm b=originalRootBlock m hm b := by
  have h := congrArg (fun P : Subgroup (originalModelFixed m)=>P.map (fixedToOriginal m hm))
    (positive_inf_negativeSimpleParabolic_eq_inversion m b)
  dsimp only at h
  rw [map_inf_eq_of_kernel_le_right (fixedToOriginal m hm) _ _
    (original_kernel_le_negativeSimpleParabolic m hm b),positive_original_image] at h
  exact h

theorem originalRootBlock_card (m : ℕ) (hm : 0<m) (b : Bool) :
    Nat.card (originalRootBlock m hm b)=(2^(2*m+1))^(if b then 2 else 1) := by
  let B := inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)
  let f := fixedToOriginal m hm
  have hi : Function.Injective (f.subgroupMap B) := by
    intro x y he
    have hxy : (f.comp (fixedPositive m).subtype) ⟨x.val,x.property.1⟩=
        (f.comp (fixedPositive m).subtype) ⟨y.val,y.property.1⟩ :=
      congrArg (fun z : B.map f=>z.val) he
    exact Subtype.ext (congrArg (fun z : fixedPositive m=>z.val)
      (fixedToOriginal_positive_injective m hm hxy))
  have hc := Nat.card_congr (Equiv.ofBijective (f.subgroupMap B)
    ⟨hi,f.subgroupMap_surjective B⟩)
  change Nat.card B=Nat.card (originalRootBlock m hm b) at hc
  rw [←hc]
  exact CFSGReeFFourSimpleInversionBlocks.simple_inversion_card m b

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootIntersections
