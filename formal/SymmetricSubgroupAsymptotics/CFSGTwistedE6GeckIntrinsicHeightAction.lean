import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightRootPermutation
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightQuotientTwist
import SymmetricSubgroupAsymptotics.CFSGFinitePermutedGroupCoordinates

/-! Intrinsic root-line coordinates carry the ACTUAL E6 height-quotient
twist. The proof checks literal one-coordinate inclusions and uses the
finite Pi universal property; no scalar chart-sign formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckHeightRootPermutation CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckHeightQuotientTwist CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateIntrinsicHeightLayer

local instance actionTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

abbrev HeightImage (K : Type) [Field K] (h : ℤ) :=
  (TailInPositive K h).map (QuotientGroup.mk' (TailInPositive K (h+1)))

theorem heightImage_twist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    (HeightImage K h).map (quotientTwist K σ h).toMonoidHom = HeightImage K h := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hy
    change quotientTwist K σ h (QuotientGroup.mk' (TailInPositive K (h + 1)) u) ∈
      HeightImage K h
    rw [quotientTwist_mk]
    have hm : positiveTwist K σ u ∈ (TailInPositive K h).map (positiveTwist K σ).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rw [tailInPositive_twist K σ h] at hm
    exact ⟨positiveTwist K σ u, hm, rfl⟩
  · exact (Nat.card_congr ((quotientTwist K σ h).subgroupMap (HeightImage K h)).toEquiv).le

def heightImageTwist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    MulAut (HeightImage K h) :=
  ((quotientTwist K σ h).subgroupMap (HeightImage K h)).trans
    (MulEquiv.subgroupCongr (heightImage_twist K σ h))

theorem heightImageTwist_val (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (x : HeightImage K h) :
    (heightImageTwist K σ h x).val = quotientTwist K σ h x.val := rfl

abbrev RootCoordinates (K : Type) [Field K] (h : ℤ) :=
  ∀k : HeightIndex h,rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val

def coordinateTwist (K : Type) [Field K] (sigma : K≃+*K) (h : ℤ) : MulAut (RootCoordinates K h) :=
  CFSGFinitePermutedGroupCoordinates.permutedPiEquiv
    (fun k : HeightIndex h=>rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val)
    (heightRootPermutation h) (rootLineTwist K sigma h)

def intrinsicCoordinates (K : Type) [Field K] (h : ℤ) (hh : 0 < h) :
    RootCoordinates K h≃*HeightImage K h :=
  intrinsicHeightLayerEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h hh

theorem intrinsicCoordinates_mulSingle (K : Type) [Field K] (h : ℤ) (hh : 0 < h)
    (k : HeightIndex h) (x : rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val) :
    (intrinsicCoordinates K h hh (Pi.mulSingle k x)).val=
      (QuotientGroup.mk' (TailInPositive K (h+1)))
        (rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
          E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val k.val.property x) :=
  intrinsicHeightLayerEquiv_mulSingle CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h hh k x

theorem coordinate_single (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (h : ℤ) (hh : 0 < h) (k : HeightIndex h)
    (x : rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val) :
    heightImageTwist K sigma h (intrinsicCoordinates K h hh (Pi.mulSingle k x))=
      intrinsicCoordinates K h hh
        (Pi.mulSingle (heightRootPermutation h k) (rootLineTwist K sigma h k x)) := by
  apply Subtype.ext
  change quotientTwist K sigma h (intrinsicCoordinates K h hh (Pi.mulSingle k x)).val=
    (intrinsicCoordinates K h hh (Pi.mulSingle (heightRootPermutation h k) (rootLineTwist K sigma h k x))).val
  rw [intrinsicCoordinates_mulSingle,intrinsicCoordinates_mulSingle,quotientTwist_mk]
  exact congrArg (QuotientGroup.mk' (TailInPositive K (h+1)))
    (rootLineInclusion_twist K sigma h k x)

theorem coordinateTwist_mulSingle (K : Type) [Field K] (sigma : K≃+*K) (h : ℤ)
    (k : HeightIndex h) (x : rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val) :
    coordinateTwist K sigma h (Pi.mulSingle k x)=
      Pi.mulSingle (heightRootPermutation h k) (rootLineTwist K sigma h k x) :=
  CFSGFinitePermutedGroupCoordinates.permutedPiEquiv_mulSingle
    (fun k : HeightIndex h=>rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val)
    (heightRootPermutation h) (rootLineTwist K sigma h) k x

theorem coordinate_intertwining_hom (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (h : ℤ) (hh : 0 < h) :
    (heightImageTwist K sigma h).toMonoidHom.comp (intrinsicCoordinates K h hh).toMonoidHom=
      (intrinsicCoordinates K h hh).toMonoidHom.comp (coordinateTwist K sigma h).toMonoidHom := by
  apply MonoidHom.pi_ext
  intro k x
  change heightImageTwist K sigma h (intrinsicCoordinates K h hh (Pi.mulSingle k x))=
    intrinsicCoordinates K h hh (coordinateTwist K sigma h (Pi.mulSingle k x))
  rw [coordinateTwist_mulSingle]
  exact coordinate_single K sigma h hh k x

theorem coordinate_intertwining (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates K h) :
    heightImageTwist K sigma h (intrinsicCoordinates K h hh c)=
      intrinsicCoordinates K h hh (coordinateTwist K sigma h c) :=
  DFunLike.congr_fun (coordinate_intertwining_hom K sigma h hh) c

theorem fixed_iff_coordinates (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (h : ℤ) (hh : 0 < h) (c : RootCoordinates K h) :
    heightImageTwist K sigma h (intrinsicCoordinates K h hh c)=intrinsicCoordinates K h hh c ↔
      ∀k,rootLineTwist K sigma h k (c k)=c (heightRootPermutation h k) := by
  rw [coordinate_intertwining]
  exact (intrinsicCoordinates K h hh).injective.eq_iff.trans
    (CFSGFinitePermutedGroupCoordinates.permutedPiEquiv_fixed_iff _ _ _ c)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckIntrinsicHeightAction
