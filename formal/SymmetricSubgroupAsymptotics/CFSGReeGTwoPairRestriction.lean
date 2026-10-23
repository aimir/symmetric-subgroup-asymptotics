import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer

/-! Literal opposed-pair automorphisms of the actual derived fixed
group restrict to automorphisms of the actual positive Ree group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestriction
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoDerivedBruhat
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveDerived
open CFSGReeGTwoDerivedPairNormalizer CFSGSubgroupFamilyStabilizer

abbrev Derived (m : ℕ) := commutator (originalModelFixed m)

def pairStabilizer (m : ℕ) (hm : 1≤m) : Subgroup (MulAut (Derived m)) :=
  familyStabilizer (fun neg:Bool=>if neg then derivedOpposite m hm
    else (derivedPositiveSylow m hm:Subgroup (Derived m)))

theorem pair_preserves_positive (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm) :
    (derivedPositiveSylow m hm:Subgroup (Derived m)).map f.val.toMonoidHom=
      derivedPositiveSylow m hm := f.property false

theorem pair_preserves_opposite (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm) :
    (derivedOpposite m hm).map f.val.toMonoidHom=derivedOpposite m hm := f.property true

def derivedPositiveEquiv (m : ℕ) (hm : 1≤m) :
    derivedPositiveSylow m hm≃*fixedPositiveGroup m where
  toFun u := ⟨u.val.val,u.property⟩
  invFun u := ⟨⟨u.val,fixedPositiveGroup_le_commutator m hm u.property⟩,u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def restrictPositive (m : ℕ) (hm : 1≤m) (f : MulAut (Derived m))
    (hf : (derivedPositiveSylow m hm:Subgroup (Derived m)).map f.toMonoidHom=
      derivedPositiveSylow m hm) : MulAut (fixedPositiveGroup m) :=
  (derivedPositiveEquiv m hm).symm.trans
    (((f.subgroupMap (derivedPositiveSylow m hm)).trans (MulEquiv.subgroupCongr hf)).trans
      (derivedPositiveEquiv m hm))

def pairRestriction (m : ℕ) (hm : 1≤m) :
    pairStabilizer m hm→*MulAut (fixedPositiveGroup m) where
  toFun f := restrictPositive m hm f.val (pair_preserves_positive m hm f)
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl

theorem pairRestriction_val (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm)
    (u : fixedPositiveGroup m) :
    (pairRestriction m hm f u).val=
      (f.val ⟨u.val,fixedPositiveGroup_le_commutator m hm u.property⟩).val := rfl

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestriction
