import SymmetricSubgroupAsymptotics.CFSGSerreTripleFixedRoots
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-! The literal triality cycle 0→2→3→0 gives original fixed-subgroup
root words over the cubic extension. This proves actual fixed membership
for both signs and arbitrary extension-field parameters. Derived
membership and a full fixed-group presentation remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration

theorem extension_three_card (q : CFSG.PrimePower) :
    Nat.card (q.Extension 3)=q.order^3 := by
  change Nat.card (GaloisField q.prime (3*q.exponent))=(q.prime^q.exponent)^3
  rw [GaloisField.card q.prime (3*q.exponent) (by have:=q.exponent_pos;omega),←pow_mul]
  rw [Nat.mul_comm 3 q.exponent]

theorem extension_three_pow_thrice (q : CFSG.PrimePower) (t : q.Extension 3) :
    ((t^q.order)^q.order)^q.order=t := by
  letI : Fintype (q.Extension 3):=Fintype.ofFinite _
  calc
    _=t^(q.order^3) := by simp only [pow_succ,pow_zero,pow_one,pow_mul]
    _=t^Nat.card (q.Extension 3) := by rw [extension_three_card]
    _=t := by simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card t

abbrev Fixed (q : CFSG.PrimePower) :=
  fixedSubgroup (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality (fun _=>q.order)

def orbitRoot (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3) : Fixed q :=
  CFSGSerreTripleFixedRoots.tripleFixedRoot (CartanMatrix.D 4) (q.Extension 3)
    CFSG.Models.triality (fun _=>q.order) neg 0 (by decide) (by decide) (by decide)
    t (extension_three_pow_thrice q t)

theorem orbitRoot_toModel (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3) :
    CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.D 4) (q.Extension 3)
      CFSG.Models.triality (fun _=>q.order) (orbitRoot q neg t)=
        modelRoot (CartanMatrix.D 4) (q.Extension 3) neg 0 t*
          modelRoot (CartanMatrix.D 4) (q.Extension 3) neg 2 (t^q.order)*
          modelRoot (CartanMatrix.D 4) (q.Extension 3) neg 3 ((t^q.order)^q.order) := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
