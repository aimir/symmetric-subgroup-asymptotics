import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedOppositeSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality

/-! The actual derived positive Sylow survives faithfully in the
literal original ReeF4 full central quotient. Disjoint opposed Sylows
kill its central 2-kernel; no whole-U or generation claim is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveCentralQuotient
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourDerivedPositiveSylow
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourDerivedOppositeSylow
open CFSGDisjointSylowProjectiveCardinality
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def positiveReeHom (m : ℕ) (hm : 0<m) :
    derivedPositiveSylow m hm→*CFSG.Models.ReeF4 m :=
  (derivedReeHom m).comp (derivedPositiveSylow m hm : Subgroup
    (commutator (originalModelFixed m))).subtype

theorem positiveReeHom_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (positiveReeHom m hm) :=
  (originalReeEquiv m).symm.injective.comp
    (central_quotient_injective (derivedPositiveSylow m hm) (derivedNegativeSylow m hm)
      (derived_opposite_sylows_inf m hm))

theorem positiveReeHom_range (m : ℕ) (hm : 0<m) :
    (positiveReeHom m hm).range=(reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) := by
  change ((derivedReeHom m).comp (derivedPositiveSylow m hm : Subgroup
    (commutator (originalModelFixed m))).subtype).range=
      (derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m))).map
        (derivedReeHom m)
  rw [MonoidHom.range_comp,Subgroup.range_subtype]

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveCentralQuotient
