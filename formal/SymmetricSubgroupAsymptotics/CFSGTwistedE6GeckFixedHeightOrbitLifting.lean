import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSourceUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckIntrinsicHeightAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange

/-! Every SINGLE orbit factor of an actual fixed E6 height coordinate
has a representative in the same height tail with an original fixed-source
action witness. Both singleton and paired representatives are constructed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGTwistedE6GeckFixedSourceUpper CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6WeylChamber
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootElementRange
open CFSGSerreOrdinaryTwists

local instance orbitTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

def heightClass (K : Type) [Field K] (h : ℤ) : Positive K →* Quotient K h :=
  QuotientGroup.mk' (TailInPositive K (h+1))

theorem rootLinePositive_mem_tail (K : Type) [Field K] (h : ℤ) (k : HeightIndex h)
    (x : RootLine K k.val.val) : rootLinePositive K k.val x∈TailInPositive K h := by
  obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K k.val.val x.val).mp x.property
  change x.val∈heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h
  rw [←ha]
  exact rootElement_mem_heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K h k.val.val k.val.property (le_of_eq k.property.symm) a

theorem rootLinePositive_twist (K : Type) [Field K] (sigma : K≃+*K)
    (h : ℤ) (k : HeightIndex h) (x : RootLine K k.val.val) :
    positiveTwist K sigma (rootLinePositive K k.val x)=
      rootLinePositive K (heightRootPermutation h k).val (rootLineTwist K sigma h k x) := rfl

theorem heightClass_single (K : Type) [Field K] (h : ℤ) (hh : 0 < h)
    (k : HeightIndex h) (x : RootLine K k.val.val) :
    heightClass K h (rootLinePositive K k.val x)=
      (intrinsicCoordinates K h hh (Pi.mulSingle k x)).val :=
  (intrinsicCoordinates_mulSingle K h hh k x).symm

theorem fixed_singleton_orbit_lift (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (c : RootCoordinates (q.Extension 2) h)
    (hc : ∀k,rootLineTwist (q.Extension 2) (definingFieldAutomorphism q 2) h k (c k)=
      c (heightRootPermutation h k))
    (k : HeightIndex h) (hk : heightRootPermutation h k=k) :
    ∃u : Positive (q.Extension 2),u∈fixedSourceUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
      heightClass (q.Extension 2) h u=
        (intrinsicCoordinates (q.Extension 2) h hh (Pi.mulSingle k (c k))).val := by
  have hroot : diagramRoot k.val.val=k.val.val :=
    congrArg (fun j : HeightIndex h=>j.val.val) hk
  have hx := congrArg Subtype.val (hc k)
  change unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) (c k).val=
    (c (heightRootPermutation h k)).val at hx
  rw [hk] at hx
  exact ⟨rootLinePositive (q.Extension 2) k.val (c k),
    singleton_mem_fixedSourceUpper q k.val hroot (c k) hx,
    rootLinePositive_mem_tail (q.Extension 2) h k (c k),
    heightClass_single (q.Extension 2) h hh k (c k)⟩

theorem fixed_paired_orbit_lift (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (c : RootCoordinates (q.Extension 2) h)
    (hc : ∀k,rootLineTwist (q.Extension 2) (definingFieldAutomorphism q 2) h k (c k)=
      c (heightRootPermutation h k))
    (k : HeightIndex h) (hk : heightRootPermutation h k≠k) :
    ∃u : Positive (q.Extension 2),u∈fixedSourceUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
      heightClass (q.Extension 2) h u=
        (intrinsicCoordinates (q.Extension 2) h hh
          (Pi.mulSingle k (c k)*Pi.mulSingle (heightRootPermutation h k)
            (c (heightRootPermutation h k)))).val := by
  have hroot : diagramRoot k.val.val≠k.val.val := by
    intro he
    apply hk
    apply Subtype.ext
    apply Subtype.ext
    exact he
  let a := rootLinePositive (q.Extension 2) k.val (c k)
  let tau := positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
  have hpartner : tau a=rootLinePositive (q.Extension 2)
      (heightRootPermutation h k).val (c (heightRootPermutation h k)) := by
    change positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (rootLinePositive (q.Extension 2) k.val (c k))=_
    rw [rootLinePositive_twist,hc k]
  refine ⟨a*tau a,pair_mem_fixedSourceUpper q k.val hroot (c k),?_,?_⟩
  · apply (TailInPositive (q.Extension 2) h).mul_mem
    · exact rootLinePositive_mem_tail (q.Extension 2) h k (c k)
    · rw [hpartner]
      exact rootLinePositive_mem_tail (q.Extension 2) h (heightRootPermutation h k)
        (c (heightRootPermutation h k))
  · rw [map_mul,hpartner,map_mul]
    change heightClass (q.Extension 2) h a*
      heightClass (q.Extension 2) h
        (rootLinePositive (q.Extension 2) (heightRootPermutation h k).val
          (c (heightRootPermutation h k)))=
      (intrinsicCoordinates (q.Extension 2) h hh (Pi.mulSingle k (c k))).val*
        (intrinsicCoordinates (q.Extension 2) h hh
          (Pi.mulSingle (heightRootPermutation h k) (c (heightRootPermutation h k)))).val
    exact congrArg₂ (·*·) (heightClass_single (q.Extension 2) h hh k (c k))
      (heightClass_single (q.Extension 2) h hh (heightRootPermutation h k)
        (c (heightRootPermutation h k)))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightOrbitLifting
