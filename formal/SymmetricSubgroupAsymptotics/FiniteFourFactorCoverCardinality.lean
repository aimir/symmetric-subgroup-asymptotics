import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-! An upper cardinal bound from an actual finite four-factor cover.
Neither uniqueness of factors nor a group-order formula is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

theorem card_le_of_cover {G I : Type*} [Group G] [Finite G] [Finite I]
    (U D V : Subgroup G) (w : I→G)
    (hcover : ∀g:G,∃(u:U)(d:D)(i:I)(v:V),g=u.val*d.val*w i*v.val) :
    Nat.card G≤Nat.card U*Nat.card D*Nat.card I*Nat.card V := by
  let encode : U×(D×(I×V))→G := fun p=>p.1.val*p.2.1.val*w p.2.2.1*p.2.2.2.val
  have hs : Function.Surjective encode := by
    intro g
    obtain ⟨u,d,i,v,he⟩ := hcover g
    exact ⟨(u,d,i,v),he.symm⟩
  have hb := Nat.card_le_card_of_surjective encode hs
  simpa only [Nat.card_prod,Nat.mul_assoc] using hb

end SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality
