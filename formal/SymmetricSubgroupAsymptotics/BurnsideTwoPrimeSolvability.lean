import SymmetricSubgroupAsymptotics.External.Burnside.Burnside
import SymmetricSubgroupAsymptotics.PublishedBurnsideTwoPrimeSolvability

/-!
# Burnside's two-prime solvability theorem, proved

The character-theoretic proof is ported from the public Apache-2.0
`odd-order-lean` submission at commit
`22f7b889b7919c0487057b928079b79baf4f2e00`. The local port preserves the
prime-equality case and works on the actual arbitrary finite group.
This constructor discharges the existing literature interface; it does not
introduce a new assumption or a finite-catalogue premise.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- Burnside's `p^a q^b` theorem supplies the former published input. -/
def burnsideTwoPrimeSolvability : PublishedBurnsideTwoPrimeSolvabilityInput where
  solvable G _ _ p q a b hp hq hcard := by
    letI : Fact p.Prime := ⟨hp⟩
    letI : Fact q.Prime := ⟨hq⟩
    exact burnside_solvable (p := p) (q := q) (a := a) (b := b) hcard

end SymmetricSubgroupAsymptotics
