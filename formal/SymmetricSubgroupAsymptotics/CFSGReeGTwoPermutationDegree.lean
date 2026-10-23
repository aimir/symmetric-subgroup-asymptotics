import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedCenter
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexPointUpper
import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree

/-! A literal central root line in the derived original fixed group
has all square scalar conjugations there. Since q is three modulo four,
inversion fills the other scalar class for fixed-point counts. Thus
every proper subgroup of the simple pinned original Ree model has
index at least q, without assuming the full fixed group is perfect. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
open PrimitiveSocleRawStructure CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveDerived
open CFSGReeGTwoPositiveCentre CFSGReeGTwoOriginalTorus CFSGReeGTwoOppositionTorus
open CFSGReeGTwoFixedCardinalitySylow CFSGReeGTwoDerivedCenter
attribute [local instance] fixedModel_finite

theorem field_card_mod_four (m : ℕ) : Nat.card (Field m)%4=3 := by
  rw [field_card,pow_add,pow_mul]
  norm_num [Nat.mul_mod,Nat.pow_mod]

def centralDerivedHom (m : ℕ) (hm : 1≤m) :
    Multiplicative (Field m)→*commutator (originalModelFixed m) :=
  ((fixedPositiveGroup m).subtype.comp (centralHom m)).codRestrict
    (commutator (originalModelFixed m))
    (fun a=>fixedPositiveGroup_le_commutator m hm (centralHom m a).property)

theorem centralDerivedHom_val (m : ℕ) (hm : 1≤m) (a : Multiplicative (Field m)) :
    (centralDerivedHom m hm a).val=(centralHom m a).val := rfl

theorem centralDerivedHom_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (centralDerivedHom m hm) := by
  intro a b hab
  apply centralHom_injective m
  apply Subtype.ext
  exact congrArg (fun d:commutator (originalModelFixed m)=>d.val) hab

def squareTorusDerived (m : ℕ) (t : (Field m)ˣ) : commutator (originalModelFixed m) :=
  ⟨fixedTorusHom m (t^2),fixedTorus_square_mem_commutator m t⟩

theorem squareTorusDerived_action (m : ℕ) (hm : 1≤m) (t : (Field m)ˣ) (a : Field m) :
    squareTorusDerived m t*centralDerivedHom m hm (Multiplicative.ofAdd a)*
      (squareTorusDerived m t)⁻¹=
    centralDerivedHom m hm (Multiplicative.ofAdd (a*(t:Field m)^2)) := by
  apply Subtype.ext
  change fixedTorusHom m (t^2)*(centralHom m (Multiplicative.ofAdd a)).val*
    (fixedTorusHom m (t^2))⁻¹=
    (centralHom m (Multiplicative.ofAdd (a*(t:Field m)^2))).val
  have h := congrArg (fun u:fixedPositiveGroup m=>u.val) (torusAction_centralHom m (t^2) a)
  dsimp only at h
  rw [fixedPositiveTorusAut_val] at h
  simpa only [Units.val_pow_eq_pow_val] using h

def originalCentralHom (m : ℕ) (hm : 1≤m) : Multiplicative (Field m)→*CFSG.Models.ReeG2 m :=
  (originalReeEquivDerived m hm).symm.toMonoidHom.comp (centralDerivedHom m hm)

theorem originalCentralHom_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (originalCentralHom m hm) :=
  (originalReeEquivDerived m hm).symm.injective.comp (centralDerivedHom_injective m hm)

def originalSquareTorus (m : ℕ) (hm : 1≤m) (t : (Field m)ˣ) : CFSG.Models.ReeG2 m :=
  (originalReeEquivDerived m hm).symm (squareTorusDerived m t)

theorem originalSquareTorus_action (m : ℕ) (hm : 1≤m) (t : (Field m)ˣ) (a : Field m) :
    originalSquareTorus m hm t*originalCentralHom m hm (Multiplicative.ofAdd a)*
      (originalSquareTorus m hm t)⁻¹=
    originalCentralHom m hm (Multiplicative.ofAdd (a*(t:Field m)^2)) := by
  have h := congrArg (originalReeEquivDerived m hm).symm (squareTorusDerived_action m hm t a)
  simpa only [map_mul,map_inv] using h

theorem field_card_le_proper_index (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (H : Subgroup (CFSG.Models.ReeG2 m)) (hH : H≠⊤) :
    3^(2*m+1)≤H.index := by
  letI : Finite (CFSG.Models.ReeG2 m) :=
    Finite.of_equiv (commutator (originalModelFixed m)) (originalReeEquivDerived m hm).symm.toEquiv
  rw [←field_card]
  change Nat.card (Field m)≤Nat.card (CFSG.Models.ReeG2 m⧸H)
  apply CFSGSquareScalarPermutationDegree.field_card_le_of_root_movement
    (field_card_mod_four m) (originalCentralHom m hm) (originalSquareTorus m hm)
    (originalSquareTorus_action m hm)
  apply CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
  intro he
  have h := originalCentralHom_injective m hm
    (he.trans (map_one (originalCentralHom m hm)).symm)
  exact (one_ne_zero : (1:Field m)≠0) (congrArg Multiplicative.toAdd h)

theorem field_card_le_leastProperIndex (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeG2 m) ell) : 3^(2*m+1)≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact field_card_le_proper_index m hm H hH

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
