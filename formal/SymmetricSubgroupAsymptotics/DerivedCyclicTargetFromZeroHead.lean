import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHead
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadZeroAbsorption

/-!
# Derived cyclic targets from exact zero relative heads

When the first derived subgroup is an elementary normal `p`-section, the
absorption field of `DerivedCyclicTarget` is not separate group-specific
data.  Vanishing of the complete relative head on every ambient-normal
subsection implies exact mixed-commutator absorption by
`PrimeRelativeHeadZeroAbsorption`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead

variable {Q : Type*} [Group Q] [Finite Q]
  {V : Subgroup Q} [V.Normal] {p : ℕ} [Fact p.Prime]

/-- Build the first-derived cyclic target while deriving every absorption
condition from literal zero relative heads. -/
def DerivedCyclicTarget.ofFirstDerivedZeroRelativeHeads
    (hderived : derivedSeries Q 1 = V)
    (hexponent : ∀ v : V, v ^ p = 1)
    (hzero : ∀ (W : Subgroup Q) [W.Normal], W ≤ V →
      Module.finrank (ZMod p) (primeRelativeCharacters p W) = 0)
    (character : V →* Multiplicative (ZMod p))
    (self_centralizing : ∀ q : Q,
      (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (separating : ∀ v : V,
      (∀ q : Q, character (MulAut.conjNormal q v) = 1) → v = 1) :
    DerivedCyclicTarget Q V 0 p where
  derived_eq := by simpa using hderived
  character := character
  self_centralizing := self_centralizing
  absorbing := by
    intro W hW hWV
    letI : W.Normal := hW
    have hWexp : ∀ w : W, w ^ p = 1 := by
      intro w
      apply Subtype.ext
      exact congrArg (fun z : V => (z : Q))
        (hexponent ⟨w, hWV w.2⟩)
    have habs := le_mixedCommutator_of_exponent_prime_relativeHead_zero
      p W hWexp (hzero W hWV)
    simpa only [derivedSeries_zero, Subgroup.commutator_comm] using habs
  separating := separating

end DerivedHead
end SymmetricSubgroupAsymptotics

end
