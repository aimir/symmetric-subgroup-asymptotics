import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightClassLifting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm
import SymmetricSubgroupAsymptotics.CFSGFiniteFixedFiltration

/-! The ENTIRE actual twist-fixed upper E6 group has ORIGINAL fixed-source
action witnesses. Actual fixed height-class representatives are peeled
through the finite integral-height filtration. No source faithfulness,
fixed-point surjectivity premise, or derived-source coverage is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage
open CFSGTwistedE6GeckFixedHeightClassLifting CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGTwistedE6GeckFixedSourceUpper CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightQuotientTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightBound
open CFSGNormTwoCoordinatePositiveHeightNormalForm

local instance sourceTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

def fixedPositive (q : CFSG.PrimePower) : Subgroup (Positive (q.Extension 2)) :=
  (positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)).toMonoidHom.eqLocus
    (MonoidHom.id (Positive (q.Extension 2)))

private theorem fixed_kernel_remainder {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (F : MulAut G) (u a : G)
    (hu : F u=u) (ha : F a=a) (he : f a=f u) :
    a⁻¹*u∈f.ker ∧ F (a⁻¹*u)=a⁻¹*u ∧ u=a*(a⁻¹*u) := by
  refine ⟨?_,?_,(mul_inv_cancel_left a u).symm⟩
  · change f (a⁻¹*u)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  · rw [map_mul,map_inv,ha,hu]

theorem exists_fixed_source_height_factor (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (u : Positive (q.Extension 2)) (hu : u∈TailInPositive (q.Extension 2) h)
    (hfix : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u) :
    ∃a : Positive (q.Extension 2),a∈fixedSourceUpper q ∧
      ∃v : Positive (q.Extension 2),v∈TailInPositive (q.Extension 2) (h+1) ∧
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) v=v ∧ u=a*v := by
  let x : HeightImage (q.Extension 2) h := ⟨heightClass (q.Extension 2) h u,⟨u,hu,rfl⟩⟩
  have hx : heightImageTwist (q.Extension 2) (definingFieldAutomorphism q 2) h x=x := by
    apply Subtype.ext
    change quotientTwist (q.Extension 2) (definingFieldAutomorphism q 2) h
      (QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1)) u)=
        QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1)) u
    rw [quotientTwist_mk,hfix]
  obtain ⟨a,ha,_,he⟩ := fixed_height_class_lift q h hh x hx
  have haf := fixedSourceUpper_fixed q a ha
  have hr := fixed_kernel_remainder (heightClass (q.Extension 2) h)
    (positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)) u a hfix haf he
  have hv : a⁻¹*u∈TailInPositive (q.Extension 2) (h+1) := by
    have hk := hr.1
    change a⁻¹*u∈(QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1))).ker at hk
    rw [QuotientGroup.ker_mk'] at hk
    exact hk
  exact ⟨a,ha,a⁻¹*u,hv,hr.2.1,hr.2.2⟩

theorem first_tail_eq_top (K : Type) [Field K] : TailInPositive K 1=⊤ := by
  apply le_antisymm le_top
  intro u _
  change u.val∈heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 1
  rw [heightTail_one_eq_positive]
  exact u.property

theorem terminal_tail_eq_bot (K : Type) [Field K] :
    TailInPositive K ((rootHeightBound CartanMatrix.E₆ : ℤ)+1)=⊥ := by
  apply le_antisymm
  · intro u hu
    change u.val∈heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
        ((rootHeightBound CartanMatrix.E₆ : ℤ)+1) at hu
    rw [final_heightTail_eq_bot,Subgroup.mem_bot] at hu
    apply Subtype.ext
    exact hu
  · exact bot_le

theorem fixedPositive_eq_fixedSourceUpper (q : CFSG.PrimePower) :
    fixedPositive q=fixedSourceUpper q := by
  apply le_antisymm
  · intro u hu
    exact CFSGFiniteFixedFiltration.fixed_mem_of_positive_step
      (positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)) (fixedSourceUpper q)
      (TailInPositive (q.Extension 2)) (rootHeightBound CartanMatrix.E₆)
      (first_tail_eq_top (q.Extension 2)) (terminal_tail_eq_bot (q.Extension 2))
      (exists_fixed_source_height_factor q) u hu
  · intro u hu
    exact fixedSourceUpper_fixed q u hu

theorem exists_original_fixed_positive_action (q : CFSG.PrimePower)
    (u : Positive (q.Extension 2))
    (hu : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u) :
    ∃s : Fixed q,imageAction q s=positiveAction (q.Extension 2) u := by
  apply (mem_fixedSourceUpper_iff q u).mp
  rw [←fixedPositive_eq_fixedSourceUpper]
  exact hu

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage
