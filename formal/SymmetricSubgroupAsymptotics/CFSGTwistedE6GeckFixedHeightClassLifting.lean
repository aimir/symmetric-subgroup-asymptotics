import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightOrbitLifting
import SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionGroupSubgroup
import Mathlib.Data.Fintype.EquivFin

/-! EVERY fixed exact-height class has an actual fixed upper representative
with an ORIGINAL fixed-source action witness. The finite involution-orbit
product combines the already constructed singleton and paired sections.
No twist-stable total root order or fixed-class lifting input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightClassLifting
open CFSGTwistedE6GeckFixedHeightOrbitLifting CFSGTwistedE6GeckFixedSourceUpper
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckSectionRootParameters CFSGNormTwoCoordinateIntrinsicHeightLayer
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateRootHeightFiltration CFSGSerreOrdinaryTwists

local instance classTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

local instance heightIndexDecEq (h : ℤ) : DecidableEq (HeightIndex h) := inferInstance

local instance heightIndexOrder (h : ℤ) : LinearOrder (HeightIndex h) :=
  LinearOrder.lift' (Fintype.equivFin (HeightIndex h)) (Fintype.equivFin (HeightIndex h)).injective

def sourceClassSubgroup (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h) :
    Subgroup (RootCoordinates (q.Extension 2) h) :=
  ((fixedSourceUpper q⊓TailInPositive (q.Extension 2) h).map (heightClass (q.Extension 2) h)).comap
    ((HeightImage (q.Extension 2) h).subtype.comp
      (intrinsicCoordinates (q.Extension 2) h hh).toMonoidHom)

theorem mem_sourceClassSubgroup_iff (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (c : RootCoordinates (q.Extension 2) h) :
    c∈sourceClassSubgroup q h hh ↔
      ∃u : Positive (q.Extension 2),u∈fixedSourceUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
        heightClass (q.Extension 2) h u=(intrinsicCoordinates (q.Extension 2) h hh c).val := by
  constructor
  · rintro ⟨u,⟨hs,ht⟩,he⟩
    exact ⟨u,hs,ht,he⟩
  · rintro ⟨u,hs,ht,he⟩
    exact ⟨u,⟨hs,ht⟩,he⟩

theorem singleton_mem_sourceClassSubgroup (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (c : RootCoordinates (q.Extension 2) h)
    (hc : ∀k,rootLineTwist (q.Extension 2) (definingFieldAutomorphism q 2) h k (c k)=
      c (heightRootPermutation h k)) (k : HeightIndex h) (hk : heightRootPermutation h k=k) :
    Pi.mulSingle k (c k)∈sourceClassSubgroup q h hh :=
  (mem_sourceClassSubgroup_iff q h hh _).mpr (fixed_singleton_orbit_lift q h hh c hc k hk)

theorem pair_mem_sourceClassSubgroup (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (c : RootCoordinates (q.Extension 2) h)
    (hc : ∀k,rootLineTwist (q.Extension 2) (definingFieldAutomorphism q 2) h k (c k)=
      c (heightRootPermutation h k)) (k : HeightIndex h) (hk : heightRootPermutation h k≠k) :
    Pi.mulSingle k (c k)*Pi.mulSingle (heightRootPermutation h k)
      (c (heightRootPermutation h k))∈sourceClassSubgroup q h hh :=
  (mem_sourceClassSubgroup_iff q h hh _).mpr (fixed_paired_orbit_lift q h hh c hc k hk)

theorem coordinate_mem_of_singleton_pair (K : Type) [Field K] (h : ℤ)
    (S : Subgroup (RootCoordinates K h)) (c : RootCoordinates K h)
    (hsingle : ∀k,heightRootPermutation h k=k → Pi.mulSingle k (c k)∈S)
    (hpair : ∀k,heightRootPermutation h k≠k → Pi.mulSingle k (c k)*
      Pi.mulSingle (heightRootPermutation h k) (c (heightRootPermutation h k))∈S) : c∈S := by
  exact CFSGFiniteInvolutionGroupSubgroup.mem_of_singleton_pair_mem (d := heightIndexDecEq h)
    (fun j : HeightIndex h=>RootLine K j.val.val)
    (heightRootPermutation h) (heightRootMap_involutive h) S c hsingle hpair

theorem fixed_coordinates_have_source_representative (q : CFSG.PrimePower)
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates (q.Extension 2) h)
    (hc : ∀k,rootLineTwist (q.Extension 2) (definingFieldAutomorphism q 2) h k (c k)=
      c (heightRootPermutation h k)) :
    ∃u : Positive (q.Extension 2),u∈fixedSourceUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
      heightClass (q.Extension 2) h u=(intrinsicCoordinates (q.Extension 2) h hh c).val := by
  apply (mem_sourceClassSubgroup_iff q h hh c).mp
  apply coordinate_mem_of_singleton_pair (q.Extension 2) h (sourceClassSubgroup q h hh) c
  · intro k hk
    exact singleton_mem_sourceClassSubgroup q h hh c hc k hk
  · intro k hk
    exact pair_mem_sourceClassSubgroup q h hh c hc k hk

theorem fixed_height_class_lift (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (x : HeightImage (q.Extension 2) h)
    (hx : heightImageTwist (q.Extension 2) (definingFieldAutomorphism q 2) h x=x) :
    ∃u : Positive (q.Extension 2),u∈fixedSourceUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
      heightClass (q.Extension 2) h u=x.val := by
  let c := (intrinsicCoordinates (q.Extension 2) h hh).symm x
  have he : intrinsicCoordinates (q.Extension 2) h hh c=x :=
    (intrinsicCoordinates (q.Extension 2) h hh).apply_symm_apply x
  have hc := (fixed_iff_coordinates (q.Extension 2) (definingFieldAutomorphism q 2) h hh c).mp
    (by rw [he];exact hx)
  obtain ⟨u,hs,ht,hu⟩ := fixed_coordinates_have_source_representative q h hh c hc
  exact ⟨u,hs,ht,hu.trans (congrArg Subtype.val he)⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightClassLifting
