import SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
import SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone

/-! Exact primary middle-binomial bounds for a DIVISOR of the actual
induction index. The literal Sylow-orbit exponents can exceed the divisor
exponent, and normalized-binomial monotonicity is what makes the same
coefficient apply to all of them. No prime-power-index equality is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

/-- The exact central-binomial coefficient is valid whenever the
displayed primary power divides the literal subgroup index. -/
theorem primary_choose_divisor (e : ℕ) (hdiv : p^e ∣ H.index) :
    (capacity H rho : ℝ) ≤ (Module.finrank (ZMod p) V : ℝ)*H.index*
      ((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1)) := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  have hbound := le_of_sylow_middle H rho P j hj hs
    (((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1))) (by
      intro q
      have heval : e ≤ H.index.factorization p :=
        ((Fact.out : p.Prime).pow_dvd_iff_le_factorization H.index_ne_zero_of_finite).mp hdiv
      simpa only [mul_div_assoc] using
        CentralBinomialNormalizedAntitone.primeGrid_primary_choose p (j q) e
          (Fact.out : p.Prime).pos (heval.trans (hval q)))
  simpa only [mul_div_assoc] using hbound

end SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
