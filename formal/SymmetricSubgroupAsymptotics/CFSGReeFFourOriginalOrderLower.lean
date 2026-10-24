import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerived
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveCentralQuotient

/-! Opposed actual Sylow subgroups give the order lower bound on the
same original full-centre quotient. Mutual disjointness after quotient
is supplied by the proved central p-element theorem; two separate
injectivity assertions alone would not suffice. The Tits parameter
is excluded because the full positive group is used inside the derived group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourDerivedPositiveSylow
open CFSGReeFFourDerivedOppositeSylow CFSGReeFFourPositiveDerived
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourFixedAmbientHom
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem derivedPositiveSylow_card (m : ℕ) (hm : 0<m) :
    Nat.card (derivedPositiveSylow m hm)=(2^(2*m+1))^12 := by
  change Nat.card (derivedPositiveSylow m hm : Subgroup
    (commutator (originalModelFixed m)))=_
  rw [derivedPositiveSylow_coe]
  let e : derivedPositive m ≃ fixedPositive m := {
    toFun u := ⟨u.val.val,u.property⟩
    invFun u := ⟨⟨u.val,fixedPositive_le_commutator m hm u.property⟩,u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (fixedPositive_card m)

theorem original_ree_order_ge (m : ℕ) (hm : 0<m) :
    (2^(2*m+1))^24 ≤ Nat.card (CFSG.Models.ReeF4 m) := by
  have hsame : Nat.card (derivedNegativeSylow m hm)=Nat.card (derivedPositiveSylow m hm) :=
    (derivedNegativeSylow m hm).card_eq_multiplicity.trans
      (derivedPositiveSylow m hm).card_eq_multiplicity.symm
  have h := CFSGDisjointSylowProjectiveCardinality.card_mul_le_central_quotient
    (derivedPositiveSylow m hm) (derivedNegativeSylow m hm)
    (derived_opposite_sylows_inf m hm)
  rw [hsame,derivedPositiveSylow_card m hm,←pow_add] at h
  rw [Nat.card_congr (originalReeEquiv m).toEquiv]
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
