import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerived
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveCentralQuotient

/-! The full exceptional-fixed group maps to the SAME pinned original
Ree derived/full-centre quotient when m>0. The equality with its derived
subgroup is proved, and its positive restriction is injective by the
already-proved opposed-Sylow quotient argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourPositiveDerived CFSGReeFFourFixedGoodSylow
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourDerivedPositiveSylow
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourPositiveCentralQuotient

def fixedToDerived (m : ℕ) (hm : 0<m) :
    originalModelFixed m→*commutator (originalModelFixed m) :=
  (MonoidHom.id (originalModelFixed m)).codRestrict
    (commutator (originalModelFixed m)) (fun g=>by
      rw [commutator_eq_top_of_positive_le m (fixedPositive_le_commutator m hm)]
      trivial)

theorem fixedToDerived_val (m : ℕ) (hm : 0<m) (g : originalModelFixed m) :
    (fixedToDerived m hm g).val=g := rfl

theorem fixedToDerived_surjective (m : ℕ) (hm : 0<m) :
    Function.Surjective (fixedToDerived m hm) := by
  intro g
  refine ⟨g.val,?_⟩
  apply Subtype.ext
  rfl

def fixedToOriginal (m : ℕ) (hm : 0<m) :
    originalModelFixed m→*CFSG.Models.ReeF4 m :=
  (derivedReeHom m).comp (fixedToDerived m hm)

theorem fixedToOriginal_surjective (m : ℕ) (hm : 0<m) :
    Function.Surjective (fixedToOriginal m hm) :=
  (derivedReeHom_surjective m).comp (fixedToDerived_surjective m hm)

private def positiveToDerivedSylow (m : ℕ) (hm : 0<m) :
    fixedPositive m→*(derivedPositiveSylow m hm) :=
  ((fixedToDerived m hm).comp (fixedPositive m).subtype).codRestrict
    (derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m)))
    (fun u=>by
      rw [derivedPositiveSylow_coe]
      change u.val∈fixedPositive m
      exact u.property)

private theorem positiveToDerivedSylow_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (positiveToDerivedSylow m hm) := by
  intro u v he
  apply Subtype.ext
  exact congrArg (fun z : derivedPositiveSylow m hm=>z.val.val) he

theorem fixedToOriginal_positive_injective (m : ℕ) (hm : 0<m) :
    Function.Injective ((fixedToOriginal m hm).comp (fixedPositive m).subtype) := by
  exact (positiveReeHom_injective m hm).comp (positiveToDerivedSylow_injective m hm)

end SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection
