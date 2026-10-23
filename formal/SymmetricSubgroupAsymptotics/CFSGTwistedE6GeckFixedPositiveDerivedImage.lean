import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedUpperSections
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage
import SymmetricSubgroupAsymptotics.CFSGE6GeckHeightSubgroupLifting
import SymmetricSubgroupAsymptotics.CFSGFiniteFixedFiltration

/-! The ENTIRE actual fixed upper E6 group has ORIGINAL Derived fixed-
subgroup action witnesses, for every q. The actual signed A2 seed
witnesses supply every singleton/paired height section; genuine fixed
class representatives and finite height peeling finish the proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveDerivedImage
open CFSGTwistedE6GeckDerivedUpperSections CFSGTwistedE6GeckFixedPositiveSourceImage
open CFSGTwistedE6GeckFixedHeightOrbitLifting CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightBound
open CFSGExceptionalCartanPositiveDefinite

local instance derivedTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

theorem derived_fixed_height_class_lift (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (x : HeightImage (q.Extension 2) h)
    (hx : heightImageTwist (q.Extension 2) (definingFieldAutomorphism q 2) h x=x) :
    ∃u : Positive (q.Extension 2),u∈derivedUpper q ∧ u∈TailInPositive (q.Extension 2) h ∧
      heightClass (q.Extension 2) h u=x.val := by
  apply CFSGE6GeckHeightSubgroupLifting.fixed_height_class_lift (q.Extension 2)
    (definingFieldAutomorphism q 2) (derivedUpper q) ?_ ?_ h hh x hx
  · intro k hk y hy
    exact singleton_mem_derivedUpper q k hk y hy
  · intro k hk y
    exact pair_mem_derivedUpper q k hk y

private theorem fixed_kernel_remainder {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (F : MulAut G) (u a : G)
    (hu : F u=u) (ha : F a=a) (he : f a=f u) :
    a⁻¹*u∈f.ker ∧ F (a⁻¹*u)=a⁻¹*u ∧ u=a*(a⁻¹*u) := by
  refine ⟨?_,?_,(mul_inv_cancel_left a u).symm⟩
  · change f (a⁻¹*u)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  · rw [map_mul,map_inv,ha,hu]

theorem exists_derived_height_factor (q : CFSG.PrimePower) (h : ℤ) (hh : 0 < h)
    (u : Positive (q.Extension 2)) (hu : u∈TailInPositive (q.Extension 2) h)
    (hfix : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u) :
    ∃a : Positive (q.Extension 2),a∈derivedUpper q ∧
      ∃v : Positive (q.Extension 2),v∈TailInPositive (q.Extension 2) (h+1) ∧
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) v=v ∧ u=a*v := by
  let x : HeightImage (q.Extension 2) h := ⟨heightClass (q.Extension 2) h u,⟨u,hu,rfl⟩⟩
  have hx : heightImageTwist (q.Extension 2) (definingFieldAutomorphism q 2) h x=x := by
    apply Subtype.ext
    change quotientTwist (q.Extension 2) (definingFieldAutomorphism q 2) h
      (QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1)) u)=
        QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1)) u
    rw [quotientTwist_mk,hfix]
  obtain ⟨a,ha,_,he⟩ := derived_fixed_height_class_lift q h hh x hx
  have haf := derivedUpper_fixed q a ha
  have hr := fixed_kernel_remainder (heightClass (q.Extension 2) h)
    (positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)) u a hfix haf he
  have hv : a⁻¹*u∈TailInPositive (q.Extension 2) (h+1) := by
    have hk := hr.1
    change a⁻¹*u∈(QuotientGroup.mk' (TailInPositive (q.Extension 2) (h+1))).ker at hk
    rw [QuotientGroup.ker_mk'] at hk
    exact hk
  exact ⟨a,ha,a⁻¹*u,hv,hr.2.1,hr.2.2⟩

theorem fixedPositive_eq_derivedUpper (q : CFSG.PrimePower) : fixedPositive q=derivedUpper q := by
  apply le_antisymm
  · intro u hu
    exact CFSGFiniteFixedFiltration.fixed_mem_of_positive_step
      (positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)) (derivedUpper q)
      (TailInPositive (q.Extension 2)) (rootHeightBound CartanMatrix.E₆)
      (first_tail_eq_top (q.Extension 2)) (terminal_tail_eq_bot (q.Extension 2))
      (exists_derived_height_factor q) u hu
  · intro u hu
    exact derivedUpper_fixed q u hu

theorem exists_original_derived_positive_action (q : CFSG.PrimePower)
    (u : Positive (q.Extension 2))
    (hu : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u) :
    ∃d : Derived q,derivedImageAction q d=positiveAction (q.Extension 2) u := by
  have hm : u∈derivedUpper q := by rw [←fixedPositive_eq_derivedUpper];exact hu
  exact hm

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveDerivedImage
