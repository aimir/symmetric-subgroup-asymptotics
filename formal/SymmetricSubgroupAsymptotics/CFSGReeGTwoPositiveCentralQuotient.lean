import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerived
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOppositionTorus
import SymmetricSubgroupAsymptotics.CFSGReeGTwoRegularTorusSquare

/-! The actual positive group survives faithfully in the original Ree
central quotient. A regular torus SQUARE belongs to the derived group,
so a central derived element in the positive subgroup is the identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveDerived
open CFSGReeGTwoFixedTorusRegularity CFSGReeGTwoRegularTorusSquare
open CFSGReeGTwoOppositionTorus CFSGReeGTwoOriginalTorus

/-- Literal inclusion into the SAME original fixed group's derived group. -/
def positiveDerivedHom (m : ℕ) (hm : 1≤m) :
    fixedPositiveGroup m →* commutator (originalModelFixed m) :=
  (fixedPositiveGroup m).subtype.codRestrict (commutator (originalModelFixed m))
    (fun u => fixedPositiveGroup_le_commutator m hm u.property)

theorem positiveDerivedHom_val (m : ℕ) (hm : 1≤m) (u : fixedPositiveGroup m) :
    (positiveDerivedHom m hm u).val=u.val := rfl

theorem positive_central_eq_one (m : ℕ) (hm : 1≤m) (u : fixedPositiveGroup m)
    (hu : positiveDerivedHom m hm u∈Subgroup.center (commutator (originalModelFixed m))) :
    u=1 := by
  obtain ⟨t,ht,htn⟩ := exists_regular_square m hm
  let d : commutator (originalModelFixed m) :=
    ⟨fixedTorusHom m (t^2),fixedTorus_square_mem_commutator m t⟩
  have he : d*positiveDerivedHom m hm u=positiveDerivedHom m hm u*d :=
    (Subgroup.mem_center_iff.mp hu) d
  apply fixedTorus_centralizer_positive m (t^2) ht htn u
  apply mul_inv_eq_iff_eq_mul.mpr
  exact congrArg (fun z : commutator (originalModelFixed m) => z.val) he

/-- Projection to the literal full central quotient in the pinned model. -/
def positiveCentralHom (m : ℕ) (hm : 1≤m) : fixedPositiveGroup m →*
    CFSGSerreFixedModelEquivalence.DerivedCentralQuotient (originalModelFixed m) :=
  (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m)))).comp
    (positiveDerivedHom m hm)

theorem positiveCentralHom_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (positiveCentralHom m hm) := by
  apply (MonoidHom.ker_eq_bot_iff (positiveCentralHom m hm)).mp
  apply eq_bot_iff.mpr
  intro u hu
  have he : positiveDerivedHom m hm u∈Subgroup.center (commutator (originalModelFixed m)) :=
    (QuotientGroup.eq_one_iff _).mp hu
  exact (Subgroup.mem_bot).mpr (positive_central_eq_one m hm u he)

/-- Faithful positive subgroup in the actual ORIGINAL ReeG2 family. -/
def reePositiveHom (m : ℕ) (hm : 1≤m) : fixedPositiveGroup m →* CFSG.Models.ReeG2 m :=
  (originalReeEquiv m).symm.toMonoidHom.comp (positiveCentralHom m hm)

theorem reePositiveHom_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (reePositiveHom m hm) :=
  (originalReeEquiv m).symm.injective.comp (positiveCentralHom_injective m hm)

theorem reePositiveGroup_card (m : ℕ) (hm : 1≤m) :
    Nat.card (reePositiveHom m hm).range=(3^(2*m+1))^3 := by
  have hc : Nat.card (fixedPositiveGroup m)=Nat.card (reePositiveHom m hm).range :=
    Nat.card_congr (Equiv.ofInjective (reePositiveHom m hm) (reePositiveHom_injective m hm))
  exact hc.symm.trans (fixedPositiveGroup_card m)

theorem reePositiveGroup_isPGroup (m : ℕ) (hm : 1≤m) :
    IsPGroup 3 (reePositiveHom m hm).range :=
  IsPGroup.of_card ((reePositiveGroup_card m hm).trans (pow_mul 3 (2*m+1) 3).symm)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient
