import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameterMaps
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Exact fixed-field, kernel and image sizes for the original Suzuki
twist. These are finite-field cardinal consequences of the proved
Frobenius identities, with no group-classification premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters

abbrev FixedTheta (m : ℕ) := {x : Field m // theta m x=x}

theorem theta_fixed_card (m : ℕ) : Nat.card (FixedTheta m)=2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨⟨0,map_zero (theta m)⟩,⟨1,map_one (theta m)⟩,?_,?_⟩
  · intro he
    exact zero_ne_one (congrArg (fun x : FixedTheta m => x.val) he)
  · ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      rcases (theta_fixed_iff m x.val).mp x.property with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

def thetaPlusSelf (m : ℕ) : Field m →+ Field m :=
  (theta m).toAddMonoidHom+AddMonoidHom.id (Field m)

@[simp] theorem thetaPlusSelf_apply (m : ℕ) (x : Field m) :
    thetaPlusSelf m x=theta m x+x := rfl

def thetaPlusSelfKerEquiv (m : ℕ) : (thetaPlusSelf m).ker ≃ FixedTheta m where
  toFun x := ⟨x.val,by
    have hx : theta m x.val+x.val=0 := x.property
    rw [add_eq_zero_iff_eq_neg,CharTwo.neg_eq] at hx
    exact hx⟩
  invFun x := ⟨x.val,by
    change theta m x.val+x.val=0
    rw [x.property,CharTwo.add_self_eq_zero]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem thetaPlusSelf_ker_card (m : ℕ) : Nat.card (thetaPlusSelf m).ker=2 :=
  (Nat.card_congr (thetaPlusSelfKerEquiv m)).trans (theta_fixed_card m)

theorem thetaPlusSelf_range_card (m : ℕ) :
    Nat.card (thetaPlusSelf m).range=2^(2*m) := by
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (thetaPlusSelf m).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (thetaPlusSelf m)).toEquiv,
    thetaPlusSelf_ker_card,field_card,pow_succ] at hc
  omega

theorem one_not_mem_thetaPlusSelf_range (m : ℕ) :
    (1 : Field m)∉(thetaPlusSelf m).range := by
  rintro ⟨x,hx⟩
  exact theta_add_self_ne_one m x hx

end SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters
