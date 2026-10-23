import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightClassLifting

/-! Actual E6 fixed-height lifting into ANY upper subgroup containing the
literal singleton and paired orbit sections. All coordinate action,
same-tail membership and orbit assembly are proved from the actual Geck
model. Consumers must prove their displayed local section memberships. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckHeightSubgroupLifting
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveCoordinateLifts CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckFixedHeightOrbitLifting CFSGTwistedE6GeckFixedHeightClassLifting
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckHeightQuotientTwist CFSGNormTwoCoordinateRootHeightFiltration
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite

local instance subgroupTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

def classSubgroup (K : Type) [Field K] (S : Subgroup (Positive K)) (h : ℤ) (hh : 0 < h) :
    Subgroup (RootCoordinates K h) :=
  ((S⊓TailInPositive K h).map (heightClass K h)).comap
    ((HeightImage K h).subtype.comp (intrinsicCoordinates K h hh).toMonoidHom)

theorem mem_classSubgroup_iff (K : Type) [Field K] (S : Subgroup (Positive K))
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates K h) : c∈classSubgroup K S h hh ↔
    ∃u : Positive K,u∈S ∧ u∈TailInPositive K h ∧
      heightClass K h u=(intrinsicCoordinates K h hh c).val := by
  constructor
  · rintro ⟨u,⟨hs,ht⟩,he⟩
    exact ⟨u,hs,ht,he⟩
  · rintro ⟨u,hs,ht,he⟩
    exact ⟨u,⟨hs,ht⟩,he⟩

theorem singleton_mem_classSubgroup (K : Type) [Field K] (sigma : K≃+*K)
    (S : Subgroup (Positive K))
    (hsingle : ∀(k : PositiveRoot),diagramRoot k.val=k.val → ∀x : RootLine K k.val,
      unitTwist K sigma x.val=x.val → rootLinePositive K k x∈S)
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates K h)
    (hc : ∀k,rootLineTwist K sigma h k (c k)=c (heightRootPermutation h k))
    (k : HeightIndex h) (hk : heightRootPermutation h k=k) :
    Pi.mulSingle k (c k)∈classSubgroup K S h hh := by
  have hroot : diagramRoot k.val.val=k.val.val := congrArg (fun j : HeightIndex h=>j.val.val) hk
  have hx := congrArg Subtype.val (hc k)
  change unitTwist K sigma (c k).val=(c (heightRootPermutation h k)).val at hx
  rw [hk] at hx
  exact (mem_classSubgroup_iff K S h hh _).mpr
    ⟨rootLinePositive K k.val (c k),hsingle k.val hroot (c k) hx,
      rootLinePositive_mem_tail K h k (c k),heightClass_single K h hh k (c k)⟩

theorem pair_mem_classSubgroup (K : Type) [Field K] (sigma : K≃+*K)
    (S : Subgroup (Positive K))
    (hpair : ∀(k : PositiveRoot),diagramRoot k.val≠k.val → ∀x : RootLine K k.val,
      rootLinePositive K k x*positiveTwist K sigma (rootLinePositive K k x)∈S)
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates K h)
    (hc : ∀k,rootLineTwist K sigma h k (c k)=c (heightRootPermutation h k))
    (k : HeightIndex h) (hk : heightRootPermutation h k≠k) :
    Pi.mulSingle k (c k)*Pi.mulSingle (heightRootPermutation h k)
      (c (heightRootPermutation h k))∈classSubgroup K S h hh := by
  have hroot : diagramRoot k.val.val≠k.val.val := by
    intro he
    apply hk
    apply Subtype.ext
    apply Subtype.ext
    exact he
  let a := rootLinePositive K k.val (c k)
  have hpartner : positiveTwist K sigma a=
      rootLinePositive K (heightRootPermutation h k).val (c (heightRootPermutation h k)) := by
    change positiveTwist K sigma (rootLinePositive K k.val (c k))=_
    rw [rootLinePositive_twist,hc k]
  apply (mem_classSubgroup_iff K S h hh _).mpr
  refine ⟨a*positiveTwist K sigma a,hpair k.val hroot (c k),?_,?_⟩
  · apply (TailInPositive K h).mul_mem
    · exact rootLinePositive_mem_tail K h k (c k)
    · rw [hpartner]
      exact rootLinePositive_mem_tail K h (heightRootPermutation h k) (c (heightRootPermutation h k))
  · rw [map_mul,hpartner,map_mul]
    change heightClass K h a*
      heightClass K h (rootLinePositive K (heightRootPermutation h k).val (c (heightRootPermutation h k)))=
      (intrinsicCoordinates K h hh (Pi.mulSingle k (c k))).val*
        (intrinsicCoordinates K h hh
          (Pi.mulSingle (heightRootPermutation h k) (c (heightRootPermutation h k)))).val
    exact congrArg₂ (·*·) (heightClass_single K h hh k (c k))
      (heightClass_single K h hh (heightRootPermutation h k) (c (heightRootPermutation h k)))

theorem fixed_height_class_lift (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (S : Subgroup (Positive K))
    (hsingle : ∀(k : PositiveRoot),diagramRoot k.val=k.val → ∀x : RootLine K k.val,
      unitTwist K sigma x.val=x.val → rootLinePositive K k x∈S)
    (hpair : ∀(k : PositiveRoot),diagramRoot k.val≠k.val → ∀x : RootLine K k.val,
      rootLinePositive K k x*positiveTwist K sigma (rootLinePositive K k x)∈S)
    (h : ℤ) (hh : 0 < h) (x : HeightImage K h) (hx : heightImageTwist K sigma h x=x) :
    ∃u : Positive K,u∈S ∧ u∈TailInPositive K h ∧ heightClass K h u=x.val := by
  let c := (intrinsicCoordinates K h hh).symm x
  have he : intrinsicCoordinates K h hh c=x := (intrinsicCoordinates K h hh).apply_symm_apply x
  have hc := (fixed_iff_coordinates K sigma h hh c).mp (by rw [he];exact hx)
  have hm : c∈classSubgroup K S h hh := by
    apply coordinate_mem_of_singleton_pair K h (classSubgroup K S h hh) c
    · intro k hk
      exact singleton_mem_classSubgroup K sigma S hsingle h hh c hc k hk
    · intro k hk
      exact pair_mem_classSubgroup K sigma S hpair h hh c hc k hk
  obtain ⟨u,hs,ht,hu⟩ := (mem_classSubgroup_iff K S h hh c).mp hm
  exact ⟨u,hs,ht,hu.trans (congrArg Subtype.val he)⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckHeightSubgroupLifting
