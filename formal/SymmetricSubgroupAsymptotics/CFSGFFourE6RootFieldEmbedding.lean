import SymmetricSubgroupAsymptotics.CFSGFFourDiagramFieldEmbedding
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveOrbitFactors

/-! Field embedding on the SAME literal E6 root lines and folded
orbit factors. The root-parameter map is proved from the integral
selected-root polynomial identity, uniformly in all characteristics.
Consequently generated orthogonal factors may be transported before
applying full extension-field root centralization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootFieldEmbedding
open CFSGFFourDiagramFieldEmbedding CFSGFFourE6PositiveOrbitFactors
open CFSGFFourE6PositiveSections CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckOriginalRootSections CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCoordinateRootSubgroup

variable {F K : Type} [Field F] [Field K]

def rawFieldMap (iota : F→+*K) :
    (Matrix GeckIndex GeckIndex F)ˣ→*(Matrix GeckIndex GeckIndex K)ˣ := unitsFieldMap iota

theorem rawFieldMap_injective (iota : F→+*K) : Function.Injective (rawFieldMap iota) :=
  unitsFieldMap_injective iota

theorem selectedRoot_fieldMap (iota : F→+*K) (a : Roots CartanMatrix.E₆) (t : F) :
    rawFieldMap iota (selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos F a t)=
    selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K a (iota t) := by
  apply Units.ext
  exact map_selectedRootElement_val CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos iota a t

theorem rootLine_fieldMap_mem (iota : F→+*K) (a : Roots CartanMatrix.E₆)
    (x : rootLineAt F a) : rawFieldMap iota x.val∈rootLineAt K a := by
  obtain ⟨t,ht⟩ := (mem_rootSubgroup_iff_selected CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos F a x.val).mp
      x.property
  rw [←ht,selectedRoot_fieldMap]
  exact selectedRootElement_mem CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K a (iota t)

def rootLineFieldMap (iota : F→+*K) (a : Roots CartanMatrix.E₆) :
    rootLineAt F a→*rootLineAt K a :=
  ((rawFieldMap iota).comp (rootLineAt F a).subtype).codRestrict (rootLineAt K a)
    (fun x=>rootLine_fieldMap_mem iota a x)

theorem rootLineFieldMap_val (iota : F→+*K) (a : Roots CartanMatrix.E₆)
    (x : rootLineAt F a) : (rootLineFieldMap iota a x).val=rawFieldMap iota x.val := rfl

theorem rootOrbitFactor_fieldMap (iota : F→+*K) (k : PositiveRoot) (x : RootLine F k.val) :
    rawFieldMap iota (rootOrbitFactor F k x).val=
      (rootOrbitFactor K k (rootLineFieldMap iota k.val x)).val := by
  unfold rootOrbitFactor
  split_ifs
  · rfl
  · let u : (Matrix GeckIndex GeckIndex F)ˣ := rawRootUnit F k x
    change rawFieldMap iota (u*unitTwist F (RingEquiv.refl F) u)=
      rawFieldMap iota u*unitTwist K (RingEquiv.refl K) (rawFieldMap iota u)
    rw [map_mul]
    exact congrArg (fun z=>(rawFieldMap iota u)*z)
      (twist_unitsFieldMap diagramIndex iota (RingEquiv.refl K) (fun _=>rfl) u).symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootFieldEmbedding
