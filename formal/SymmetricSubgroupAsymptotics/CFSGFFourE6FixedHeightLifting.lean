import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightClassLifting

/-! Every identity-field diagram-fixed E6 height class has a representative
in the actual folded F4 subgroup. Singleton and paired root sections are
combined by the proved finite involution-orbit product theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeightLifting
open CFSGFFourSerreMatrices CFSGFFourE6PositiveSections CFSGFFourE6DiagramFixed
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveCoordinateLifts CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckFixedHeightOrbitLifting CFSGTwistedE6GeckFixedHeightClassLifting
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6WeylChamber
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateRootHeightFiltration CFSGSerreQuadraticMatrix

def foldedUpper (K : Type) [Field K] : Subgroup (Positive K) :=
  (canonicalElementaryGroup realizationData K).comap (Positive K).subtype

theorem foldedUpper_fixed (K : Type) [Field K] (u : Positive K) (hu : u∈foldedUpper K) :
    positiveTwist K (RingEquiv.refl K) u=u := by
  apply Subtype.ext
  exact foldedModel_le_diagramFixed K hu

local instance foldedTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

def foldedClassSubgroup (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    Subgroup (RootCoordinates K h) :=
  ((foldedUpper K⊓TailInPositive K h).map (heightClass K h)).comap
    ((HeightImage K h).subtype.comp (intrinsicCoordinates K h hh).toMonoidHom)

theorem mem_foldedClassSubgroup_iff (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (c : RootCoordinates K h) : c∈foldedClassSubgroup K h hh ↔
    ∃u : Positive K,u∈foldedUpper K ∧ u∈TailInPositive K h ∧
      heightClass K h u=(intrinsicCoordinates K h hh c).val := by
  constructor
  · rintro ⟨u,⟨hs,ht⟩,he⟩
    exact ⟨u,hs,ht,he⟩
  · rintro ⟨u,hs,ht,he⟩
    exact ⟨u,⟨hs,ht⟩,he⟩

theorem singleton_mem_foldedClassSubgroup (K : Type) [Field K] [Finite K]
    (h : ℤ) (hh : 0<h) (c : RootCoordinates K h) (k : HeightIndex h)
    (hk : heightRootPermutation h k=k) :
    Pi.mulSingle k (c k)∈foldedClassSubgroup K h hh := by
  have hroot : diagramRoot k.val.val=k.val.val :=
    congrArg (fun j : HeightIndex h=>j.val.val) hk
  apply (mem_foldedClassSubgroup_iff K h hh _).mpr
  exact ⟨rootLinePositive K k.val (c k),
    singleton_root_mem_folded K k.val hroot (c k),rootLinePositive_mem_tail K h k (c k),
    heightClass_single K h hh k (c k)⟩

theorem pair_mem_foldedClassSubgroup (K : Type) [Field K] [Finite K]
    (h : ℤ) (hh : 0<h) (c : RootCoordinates K h)
    (hc : ∀k,rootLineTwist K (RingEquiv.refl K) h k (c k)=c (heightRootPermutation h k))
    (k : HeightIndex h) (hk : heightRootPermutation h k≠k) :
    Pi.mulSingle k (c k)*Pi.mulSingle (heightRootPermutation h k)
      (c (heightRootPermutation h k))∈foldedClassSubgroup K h hh := by
  have hroot : diagramRoot k.val.val≠k.val.val := by
    intro he
    apply hk
    apply Subtype.ext
    apply Subtype.ext
    exact he
  let a := rootLinePositive K k.val (c k)
  let F := positiveTwist K (RingEquiv.refl K)
  have hpartner : F a=rootLinePositive K (heightRootPermutation h k).val
      (c (heightRootPermutation h k)) := by
    change positiveTwist K (RingEquiv.refl K) (rootLinePositive K k.val (c k))=_
    rw [rootLinePositive_twist,hc k]
  apply (mem_foldedClassSubgroup_iff K h hh _).mpr
  refine ⟨a*F a,paired_root_mem_folded K k.val hroot (c k),?_,?_⟩
  · apply (TailInPositive K h).mul_mem
    · exact rootLinePositive_mem_tail K h k (c k)
    · rw [hpartner]
      exact rootLinePositive_mem_tail K h (heightRootPermutation h k)
        (c (heightRootPermutation h k))
  · rw [map_mul,hpartner,map_mul]
    change heightClass K h a *
      heightClass K h (rootLinePositive K (heightRootPermutation h k).val
        (c (heightRootPermutation h k))) =
      (intrinsicCoordinates K h hh (Pi.mulSingle k (c k))).val *
        (intrinsicCoordinates K h hh (Pi.mulSingle (heightRootPermutation h k)
          (c (heightRootPermutation h k)))).val
    exact congrArg₂ (·*·) (heightClass_single K h hh k (c k))
      (heightClass_single K h hh (heightRootPermutation h k) (c (heightRootPermutation h k)))

theorem fixed_height_class_lift (K : Type) [Field K] [Finite K] (h : ℤ) (hh : 0<h)
    (x : HeightImage K h) (hx : heightImageTwist K (RingEquiv.refl K) h x=x) :
    ∃u : Positive K,u∈foldedUpper K ∧ u∈TailInPositive K h ∧ heightClass K h u=x.val := by
  let c := (intrinsicCoordinates K h hh).symm x
  have he : intrinsicCoordinates K h hh c=x := (intrinsicCoordinates K h hh).apply_symm_apply x
  have hc := (fixed_iff_coordinates K (RingEquiv.refl K) h hh c).mp (by rw [he];exact hx)
  have hm : c∈foldedClassSubgroup K h hh :=
    coordinate_mem_of_singleton_pair K h (foldedClassSubgroup K h hh) c
      (fun k hk=>singleton_mem_foldedClassSubgroup K h hh c k hk)
      (fun k hk=>pair_mem_foldedClassSubgroup K h hh c hc k hk)
  obtain ⟨u,hs,ht,hu⟩ := (mem_foldedClassSubgroup_iff K h hh c).mp hm
  exact ⟨u,hs,ht,hu.trans (congrArg Subtype.val he)⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeightLifting
