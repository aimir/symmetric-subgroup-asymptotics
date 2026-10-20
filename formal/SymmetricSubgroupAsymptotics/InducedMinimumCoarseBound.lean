import SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
import SymmetricSubgroupAsymptotics.PrimeGridMiddleElementary

/-! A coarse actual generator bound used only for the empty prime-to
support fallback in the logarithmic arithmetic. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem coarse : (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,_,hs⟩ := inducedMackeySylow_indices H p P
  have h := le_of_sylow_middle H rho P j hj hs 1 (by
    intro q
    have hw : (primeGridMiddleWidth p (j q) : ℝ)≤(p : ℝ)^j q := by
      exact_mod_cast primeGridMiddleWidth_le_card p (j q)
    simpa only [mul_one] using hw)
  simpa only [mul_one] using h

end SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
