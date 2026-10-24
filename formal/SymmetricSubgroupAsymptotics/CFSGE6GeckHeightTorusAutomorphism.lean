import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusLeading
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightQuotientTwist

/-! The literal product torus induces actual automorphisms on the
ambient E6 positive group and each height quotient. Denominator
invariance is proved from the selected-root conjugation formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusAutomorphism
open CFSGE6GeckProductTorus CFSGE6GeckProductTorusLeading CFSGE6GeckProductTorusRootAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckHeightQuotientTwist
open CFSGNormTwoCoordinateRootHeightFiltration CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

theorem positive_torus_image_eq (K : Type) [Field K] (x : Fin 6→Kˣ) :
    (Positive K).map (MulAut.conj (rawProductTorus K x)).toMonoidHom=Positive K := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp (product_torus_normalizes_positive K x)

def positiveTorus (K : Type) [Field K] (x : Fin 6→Kˣ) : MulAut (Positive K) :=
  ((MulAut.conj (rawProductTorus K x)).subgroupMap (Positive K)).trans
    (MulEquiv.subgroupCongr (positive_torus_image_eq K x))

theorem positiveTorus_val (K : Type) [Field K] (x : Fin 6→Kˣ) (u : Positive K) :
    (positiveTorus K x u).val=rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹ := rfl

theorem tailInPositive_torus_image_eq (K : Type) [Field K] [Finite K]
    (x : Fin 6→Kˣ) (h : ℤ) :
    (TailInPositive K h).map (positiveTorus K x).toMonoidHom=TailInPositive K h := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨u,hu,rfl⟩
    change (positiveTorus K x u).val∈heightTail A hd hs hp ho K h
    rw [positiveTorus_val]
    have hm : rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹∈
        (heightTail A hd hs hp ho K h).map (MulAut.conj (rawProductTorus K x)).toMonoidHom :=
      ⟨u.val,hu,rfl⟩
    rw [product_torus_heightTail_image_eq K x h] at hm
    exact hm
  · exact (Nat.card_congr ((positiveTorus K x).subgroupMap (TailInPositive K h)).toEquiv).le

def quotientTorus (K : Type) [Field K] [Finite K] (x : Fin 6→Kˣ) (h : ℤ) :
    MulAut (Quotient K h) :=
  QuotientGroup.congr (TailInPositive K (h+1)) (TailInPositive K (h+1))
    (positiveTorus K x) (tailInPositive_torus_image_eq K x (h+1))

theorem quotientTorus_mk (K : Type) [Field K] [Finite K] (x : Fin 6→Kˣ)
    (h : ℤ) (u : Positive K) :
    quotientTorus K x h (QuotientGroup.mk' (TailInPositive K (h+1)) u)=
      QuotientGroup.mk' (TailInPositive K (h+1)) (positiveTorus K x u) :=
  QuotientGroup.congr_mk' (TailInPositive K (h+1)) (TailInPositive K (h+1))
    (positiveTorus K x) (tailInPositive_torus_image_eq K x (h+1)) u

end SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusAutomorphism
