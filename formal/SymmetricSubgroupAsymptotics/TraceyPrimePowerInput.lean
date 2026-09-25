import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.PGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A precise permitted literature interface, specialized to finite
p-groups in the prime field. Tracey, "Minimal generation of transitive
permutation groups", Theorem 4.13, printed page 23, final prime-power
assertion, with local H1=H, supplies the displayed generator bound.
The coefficient in that assertion is at most the original fibre dimension.
The source is the actual induced representation, and M is its actual
subrepresentation. This input is a visible hypothesis, never an axiom.

Passing from this input to a bound on a general induced module still
requires the project's actual Sylow-orbit filtration and floor summation.
No such project recurrence is included in the input. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

def RepresentationGeneratedBy {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (n : ℕ) : Prop :=
  ∃ v : Fin n→ρ.asModule, Submodule.span k[G] (Set.range v)=⊤

/-- The integer prime-power factor, with t>0 required at every input use. -/
def traceyPrimePowerFactor (p t : ℕ) : ℕ :=
  ⌊Real.sqrt (2/Real.pi)*(p:ℝ)^t / Real.sqrt ((t:ℝ)*((p:ℝ)-1))⌋₊

/-- Published Theorem4.13, restricted to the exact original p-group
and its exact induced prime-field module. -/
def TraceyPrimePowerModuleInput (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ (H : Subgroup G) (t : ℕ), 0<t → H.index=p^t →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V],
    ∀ (ρ : Representation (ZMod p) H V) (M : Subrepresentation (ρ.ind H.subtype)),
      ∃ n : ℕ, n≤Module.finrank (ZMod p) V*traceyPrimePowerFactor p t ∧
        RepresentationGeneratedBy M.toRepresentation n

/-- Only the published input is assumed. The passage from original
module generators to the original invariant character head is proved. -/
theorem traceyPrimePower_head_bound (p : ℕ) [Fact p.Prime]
    (hTracey : TraceyPrimePowerModuleInput p)
    (G : Type) [Group G] [Finite G] (hG : IsPGroup p G)
    (H : Subgroup G) (t : ℕ) (ht : 0<t) (hindex : H.index=p^t)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) H V) (M : Subrepresentation (ρ.ind H.subtype)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation))≤
        Module.finrank (ZMod p) V*traceyPrimePowerFactor p t := by
  obtain ⟨n,hn,v,hv⟩ := hTracey G hG H t ht hindex V ρ M
  exact (representationCharacterHead_le_generators M.toRepresentation v hv).trans hn

end SymmetricSubgroupAsymptotics
