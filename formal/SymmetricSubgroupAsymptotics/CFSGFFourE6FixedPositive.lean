import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeightLifting
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage

/-! The whole identity-diagram-fixed E6 upper group is EXACTLY the
intersection of the same upper group with the actual folded F4 group.
The proved same-field root sections are peeled through the finite height
filtration; fixed-point surjectivity is a conclusion, not a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositive
open CFSGFFourE6FixedHeightLifting CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightQuotientTwist
open CFSGTwistedE6GeckFixedHeightOrbitLifting CFSGTwistedE6GeckFixedPositiveSourceImage
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightBound

def fixedUpper (K : Type) [Field K] : Subgroup (Positive K) :=
  (positiveTwist K (RingEquiv.refl K)).toMonoidHom.eqLocus (MonoidHom.id (Positive K))

local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

theorem exists_folded_height_factor (K : Type) [Field K] [Finite K] (h : ℤ) (hh : 0<h)
    (u : Positive K) (hu : u∈TailInPositive K h)
    (hfix : positiveTwist K (RingEquiv.refl K) u=u) :
    ∃a : Positive K,a∈foldedUpper K ∧ ∃v : Positive K,
      v∈TailInPositive K (h+1) ∧ positiveTwist K (RingEquiv.refl K) v=v ∧ u=a*v := by
  let x : HeightImage K h := ⟨heightClass K h u,⟨u,hu,rfl⟩⟩
  have hx : heightImageTwist K (RingEquiv.refl K) h x=x := by
    apply Subtype.ext
    change quotientTwist K (RingEquiv.refl K) h
        (QuotientGroup.mk' (TailInPositive K (h+1)) u)=
      QuotientGroup.mk' (TailInPositive K (h+1)) u
    rw [quotientTwist_mk,hfix]
  obtain ⟨a,ha,_,he⟩ := CFSGFFourE6FixedHeightLifting.fixed_height_class_lift K h hh x hx
  have haf := foldedUpper_fixed K a ha
  have hv : a⁻¹*u∈TailInPositive K (h+1) := by
    have hk : a⁻¹*u∈(heightClass K h).ker := by
      change (heightClass K h) (a⁻¹*u)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    change a⁻¹*u∈(QuotientGroup.mk' (TailInPositive K (h+1))).ker at hk
    rw [QuotientGroup.ker_mk'] at hk
    exact hk
  refine ⟨a,ha,a⁻¹*u,hv,?_,(mul_inv_cancel_left a u).symm⟩
  rw [map_mul,map_inv,haf,hfix]

theorem fixedUpper_eq_foldedUpper (K : Type) [Field K] [Finite K] :
    fixedUpper K=foldedUpper K := by
  apply le_antisymm
  · intro u hu
    exact CFSGFiniteFixedFiltration.fixed_mem_of_positive_step
      (positiveTwist K (RingEquiv.refl K)) (foldedUpper K) (TailInPositive K)
      (rootHeightBound CartanMatrix.E₆) (first_tail_eq_top K) (terminal_tail_eq_bot K)
      (exists_folded_height_factor K) u hu
  · intro u hu
    exact foldedUpper_fixed K u hu

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositive
