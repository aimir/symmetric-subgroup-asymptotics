import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient

/-! Genuine induced automorphisms of the actual positive height
quotients. The denominator invariance is proved from matrix height-tail
invariance; it is not an extra input to the fixed-coordinate argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightQuotientTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckHeightTwist
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite

abbrev TailInPositive (K : Type) [Field K] (h : ℤ) :=
  heightTailInPositive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

theorem tailInPositive_twist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    (TailInPositive K h).map (positiveTwist K σ).toMonoidHom = TailInPositive K h := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    change (positiveTwist K σ y).val ∈ HeightTail K h
    rw [positiveTwist_val]
    have hm : CFSGTwistedE6GeckMatrixTwist.unitTwist K σ y.val ∈
        (HeightTail K h).map (CFSGTwistedE6GeckMatrixTwist.unitTwist K σ).toMonoidHom :=
      ⟨y.val, hy, rfl⟩
    rw [heightTail_twist K σ h] at hm
    exact hm
  · exact (Nat.card_congr ((positiveTwist K σ).subgroupMap (TailInPositive K h)).toEquiv).le

abbrev Quotient (K : Type) [Field K] (h : ℤ) :=
  Positive K ⧸ TailInPositive K (h + 1)

def quotientTwist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    MulAut (Quotient K h) :=
  QuotientGroup.congr (TailInPositive K (h + 1)) (TailInPositive K (h + 1))
    (positiveTwist K σ) (tailInPositive_twist K σ (h + 1))

theorem quotientTwist_mk (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (u : Positive K) :
    quotientTwist K σ h (QuotientGroup.mk' (TailInPositive K (h + 1)) u) =
      QuotientGroup.mk' (TailInPositive K (h + 1)) (positiveTwist K σ u) :=
  QuotientGroup.congr_mk' (TailInPositive K (h + 1)) (TailInPositive K (h + 1))
    (positiveTwist K σ) (tailInPositive_twist K σ (h + 1)) u

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightQuotientTwist
