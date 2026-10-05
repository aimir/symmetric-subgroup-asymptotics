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

/-- An elementary prime normal subgroup with zero complete relative head is
the full first derived subgroup as soon as the quotient above it is
commutative.  The lower inclusion is the zero-head absorption theorem; the
upper inclusion is the usual commutator description of an abelian quotient. -/
theorem derivedSeries_one_eq_of_quotient_commutative_relativeHead_zero
    (hexponent : ∀ v : V, v ^ p = 1)
    (hzero : Module.finrank (ZMod p) (primeRelativeCharacters p V) = 0)
    (hquotient : IsMulCommutative (Q ⧸ V)) :
    derivedSeries Q 1 = V := by
  apply le_antisymm
  · rw [derivedSeries_one]
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotient
  · have habs : V ≤ ⁅V, (⊤ : Subgroup Q)⁆ :=
      le_mixedCommutator_of_exponent_prime_relativeHead_zero
        p V hexponent hzero
    rw [derivedSeries_one]
    exact habs.trans (Subgroup.commutator_mono le_top le_rfl)

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

/-- Build the cyclic-dual target directly from an abelian quotient.  Exact
first-derived equality and every absorption field are consequences of the
same zero relative-head hypothesis. -/
def DerivedCyclicTarget.ofAbelianQuotientZeroRelativeHeads
    (hexponent : ∀ v : V, v ^ p = 1)
    (hzero : ∀ (W : Subgroup Q) [W.Normal], W ≤ V →
      Module.finrank (ZMod p) (primeRelativeCharacters p W) = 0)
    (hquotient : IsMulCommutative (Q ⧸ V))
    (character : V →* Multiplicative (ZMod p))
    (self_centralizing : ∀ q : Q,
      (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (separating : ∀ v : V,
      (∀ q : Q, character (MulAut.conjNormal q v) = 1) → v = 1) :
    DerivedCyclicTarget Q V 0 p :=
  .ofFirstDerivedZeroRelativeHeads
    (derivedSeries_one_eq_of_quotient_commutative_relativeHead_zero
      hexponent (hzero V le_rfl) hquotient)
    hexponent hzero character self_centralizing separating

end DerivedHead
end SymmetricSubgroupAsymptotics

end
