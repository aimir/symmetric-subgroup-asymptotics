import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedGoodSylow
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! Good Sylow witnesses for the literal original twisted-A model in
every rank at least three, including q=2. The quotient is exactly the
original fixed source's actual derived subgroup modulo its actual center. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryCoordinates

theorem twistedA_shifted_goodSylowPrime (q : CFSG.PrimePower) (s : ℕ) :
    GoodSylowPrime (CFSG.Models.TwistedA (s + 3) q) q.prime := by
  letI : Finite (Fixed (s + 3) q) := originalFixed_finite q (s + 3) (by omega)
  let D := ↥(commutator (Fixed (s + 3) q))
  change GoodSylowPrime (D ⧸ Subgroup.center D) q.prime
  exact goodSylowPrime_surjective (QuotientGroup.mk' (Subgroup.center D))
    (QuotientGroup.mk'_surjective _) (originalDerived_goodSylowPrime q s)

theorem twistedA_higher_goodSylowPrime (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) :
    GoodSylowPrime (CFSG.Models.TwistedA r q) q.prime := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ r =>
      cases r with
      | zero => omega
      | succ s => exact twistedA_shifted_goodSylowPrime q s

end SymmetricSubgroupAsymptotics.CFSGReduction
