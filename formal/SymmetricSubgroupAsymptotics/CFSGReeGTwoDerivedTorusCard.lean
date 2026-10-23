import SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestriction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex

/-! The literal derived torus contains the actual squared torus and
has a faithful inner action. Its retained size pays the scalar factor
in the aligned automorphism count, with a possible factor two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedTorusCard
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoPairRestriction CFSGReeGTwoDerivedPairNormalizer
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOppositionTorus CFSGReeGTwoPermutationDegree
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveCentre CFSGReeGTwoPositiveDerived
open CFSGReeGTwoFixedCardinalitySylow
attribute [local instance] fixedModel_finite

def squareUnitGroup (m : ℕ) : Subgroup (Field m)ˣ := (powMonoidHom 2).range

def squareUnitsIntoDerivedTorus (m : ℕ) : squareUnitGroup m→*derivedTorus m where
  toFun s := ⟨⟨fixedTorusHom m s.val,by
    obtain ⟨r,hr⟩ := s.property
    rw [←hr]
    exact fixedTorus_square_mem_commutator m r⟩,⟨s.val,rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (fixedTorusHom m)
  map_mul' s t := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (fixedTorusHom m) s.val t.val

theorem squareUnitsIntoDerivedTorus_injective (m : ℕ) :
    Function.Injective (squareUnitsIntoDerivedTorus m) := by
  intro s t he
  apply Subtype.ext
  apply fixedTorusHom_injective m
  exact congrArg (fun x:derivedTorus m=>x.val.val) he

theorem units_card_le_twice_derivedTorus (m : ℕ) :
    Nat.card (Field m)ˣ≤2*Nat.card (derivedTorus m) := by
  have hi : Nat.card (squareUnitGroup m)≤Nat.card (derivedTorus m) :=
    Nat.card_le_card_of_injective (squareUnitsIntoDerivedTorus m)
      (squareUnitsIntoDerivedTorus_injective m)
  have hs : (squareUnitGroup m).index≤2 :=
    CFSGFiniteFieldSquareIndex.squares_index_le_two (Field m)
  calc
    Nat.card (Field m)ˣ=Nat.card (squareUnitGroup m)*(squareUnitGroup m).index :=
      (squareUnitGroup m).card_mul_index.symm
    _≤Nat.card (squareUnitGroup m)*2 := Nat.mul_le_mul_left _ hs
    _≤Nat.card (derivedTorus m)*2 := Nat.mul_le_mul_right 2 hi
    _=2*Nat.card (derivedTorus m) := Nat.mul_comm _ _

theorem inner_derivedTorus_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (fun t:derivedTorus m=>MulAut.conj (t:Derived m)) := by
  intro t u he
  obtain ⟨c,hc⟩ := (show t.val.val∈(fixedTorusHom m).range from t.property)
  obtain ⟨d,hd⟩ := (show u.val.val∈(fixedTorusHom m).range from u.property)
  have hcen (r : (Field m)ˣ) : fixedTorusHom m r*
      (centralHom m (Multiplicative.ofAdd (1:Field m))).val*(fixedTorusHom m r)⁻¹=
      (centralHom m (Multiplicative.ofAdd (r:Field m))).val := by
    have h := congrArg (fun z:fixedPositiveGroup m=>z.val) (torusAction_centralHom m r 1)
    dsimp only at h
    rw [fixedPositiveTorusAut_val,one_mul] at h
    exact h
  have hh := congrArg (fun A:MulAut (Derived m)=>
    (A (centralDerivedHom m hm (Multiplicative.ofAdd (1:Field m)))).val) he
  change t.val.val*(centralHom m (Multiplicative.ofAdd (1:Field m))).val*(t.val.val)⁻¹=
    u.val.val*(centralHom m (Multiplicative.ofAdd (1:Field m))).val*(u.val.val)⁻¹ at hh
  rw [←hc,←hd,hcen,hcen] at hh
  have hcd : c=d := Units.ext
    (congrArg Multiplicative.toAdd (centralHom_injective m (Subtype.ext hh)))
  apply Subtype.ext
  apply Subtype.ext
  exact hc.symm.trans ((congrArg (fixedTorusHom m) hcd).trans hd)

theorem inner_derivedTorus_mem_pair (m : ℕ) (hm : 1≤m) (t : derivedTorus m) :
    MulAut.conj (t:Derived m)∈pairStabilizer m hm := by
  have ht := derivedTorus_le_pair_normalizer m hm t.property
  intro neg
  cases neg
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.1)
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.2)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedTorusCard
