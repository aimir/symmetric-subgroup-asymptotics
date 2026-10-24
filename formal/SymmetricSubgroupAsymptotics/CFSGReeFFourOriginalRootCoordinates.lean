import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootIntersections
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusAction

/-! Literal coordinate equivalences for the intrinsic positive blocks
in the SAME original Ree quotient. The projection is proved injective
only on the positive subgroup; that suffices for both root coordinates.
The middle target is the actual Suzuki unipotent group, not its whole
rank-one ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourPerfectProjection CFSGReeFFourOuterFixedRoot
open CFSGReeFFourOriginalRootIntersections CFSGReeFFourOuterTorusAction
open CFSGReeFFourSimpleBlockPeelingGeneration CFSGReeFFourMinimalParabolics
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourMiddleSuzukiCoordinates
open CFSGReeFFourOppositionFixedPositiveNegative CFSGOpposedSubgroupPeeling

theorem original_outer_block_eq_range (m : ℕ) (hm : 0<m) :
    originalRootBlock m hm false=(originalOuterHom m hm).range := by
  change (inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m false)).map
    (fixedToOriginal m hm)=(originalOuterHom m hm).range
  rw [outer_simple_inversion_eq,MonoidHom.map_range]
  rfl

def originalOuterEquiv (m : ℕ) (hm : 0<m) :
    Multiplicative (Field m) ≃* originalRootBlock m hm false :=
  (MonoidHom.ofInjective (originalOuterHom_injective m hm)).trans
    (MulEquiv.subgroupCongr (original_outer_block_eq_range m hm).symm)

theorem originalOuterEquiv_val (m : ℕ) (hm : 0<m) (a : Multiplicative (Field m)) :
    (originalOuterEquiv m hm a).val=originalOuterHom m hm a := rfl

def middleToOriginalHom (m : ℕ) (hm : 0<m) : middleFixedSubgroup m→*CFSG.Models.ReeF4 m :=
  (fixedToOriginal m hm).comp (middleFixedSubgroup m).subtype

theorem middleToOriginalHom_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (middleToOriginalHom m hm) := by
  have hMU : middleFixedSubgroup m≤fixedPositive m := by
    rw [←middle_simple_inversion_eq]
    exact inf_le_left
  intro x y he
  have hp : ((fixedToOriginal m hm).comp (fixedPositive m).subtype) ⟨x.val,hMU x.property⟩=
      ((fixedToOriginal m hm).comp (fixedPositive m).subtype) ⟨y.val,hMU y.property⟩ := he
  exact Subtype.ext (congrArg (fun z : fixedPositive m=>z.val)
    (fixedToOriginal_positive_injective m hm hp))

theorem original_middle_block_eq_range (m : ℕ) (hm : 0<m) :
    originalRootBlock m hm true=(middleToOriginalHom m hm).range := by
  change (inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m true)).map
    (fixedToOriginal m hm)=((fixedToOriginal m hm).comp (middleFixedSubgroup m).subtype).range
  rw [middle_simple_inversion_eq,MonoidHom.range_comp,Subgroup.range_subtype]

def middleOriginalEquiv (m : ℕ) (hm : 0<m) : middleFixedSubgroup m ≃* originalRootBlock m hm true :=
  (MonoidHom.ofInjective (middleToOriginalHom_injective m hm)).trans
    (MulEquiv.subgroupCongr (original_middle_block_eq_range m hm).symm)

theorem middleOriginalEquiv_val (m : ℕ) (hm : 0<m) (g : middleFixedSubgroup m) :
    (middleOriginalEquiv m hm g).val=fixedToOriginal m hm g.val := rfl

def originalMiddleSuzukiEquiv (m : ℕ) (hm : 0<m) :
    originalRootBlock m hm true≃*CFSGSuzukiUnipotent.unipotentSubgroup m :=
  (middleOriginalEquiv m hm).symm.trans (middleSuzukiEquiv m)

theorem originalMiddleSuzukiEquiv_coordinate (m : ℕ) (hm : 0<m) (a c : Field m) :
    originalMiddleSuzukiEquiv m hm (middleOriginalEquiv m hm (middleCoordinateElement m a c))=
      CFSGSuzukiUnipotent.coordinateElement m a c := by
  change middleSuzukiEquiv m ((middleOriginalEquiv m hm).symm
    (middleOriginalEquiv m hm (middleCoordinateElement m a c)))=_
  rw [MulEquiv.symm_apply_apply]
  exact middleSuzukiEquiv_coordinateElement m a c

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootCoordinates
