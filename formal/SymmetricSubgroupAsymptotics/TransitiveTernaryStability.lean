import SymmetricSubgroupAsymptotics.TernaryStabilityArithmetic
import SymmetricSubgroupAsymptotics.TransitiveHeadDegreeInduction
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead

/-! The concrete ternary stability envelope installed on every actual
finite faithful transitive action. Primitive strict head estimates,
primitive chosen-chief weights at most degree/3, and the sharp all-action
degree-eighteen head estimate remain explicit mathematical inputs. The
entire scalar recurrence is proved in TernaryStabilityArithmetic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The primitive head input from the retained route. Degrees three/four
use the original chief series, and eighteen uses the finite bypass. -/
def PrimitiveTernaryStrictHeadBound : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    Nat.card X ≠ 3 → Nat.card X ≠ 4 → Nat.card X ≠ 18 →
      ∀ (N : Subgroup G) [N.Normal],
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3 * Nat.card X

/-- The retained finite degree-eighteen obligation concerns every
original action and every original normal subgroup, with head at most two. -/
def DegreeEighteenTernaryHeadBound : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X],
    Nat.card X = 18 → ∀ (N : Subgroup G) [N.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2

theorem primitiveTernary_stability_input
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound) :
    PrimitiveTernaryHeadBoundOutside ternaryStabilityBound ({18} : Finset ℕ) := by
  intro G X _ _ _ _ _ _ _ hF N _
  have h18 : Nat.card X ≠ 18 := by simpa only [Finset.mem_singleton] using hF
  by_cases h3 : Nat.card X = 3
  · obtain ⟨c, hc⟩ := hChief G X
    have hd := (primeRelativeHead_le_actualChiefWeight N c).trans hc
    simpa [h3, ternaryStabilityBound] using hd
  by_cases h4 : Nat.card X = 4
  · obtain ⟨c, hc⟩ := hChief G X
    have hd := (primeRelativeHead_le_actualChiefWeight N c).trans hc
    simpa [h4, ternaryStabilityBound] using hd
  exact (ternaryStrictHead_le_stability_base _ _ (hPrimitive G X h3 h4 h18 N)).trans
    (ternaryStability_base_le _ h18)

theorem degreeEighteen_stability_bypass (h18 : DegreeEighteenTernaryHeadBound) :
    FiniteDegreeTernaryHeadBound ternaryStabilityBound ({18} : Finset ℕ) := by
  intro G X _ _ _ _ _ _ _ hF N _
  have hX : Nat.card X = 18 := by simpa only [Finset.mem_singleton] using hF
  simpa only [hX, ternaryStabilityBound_eighteen] using h18 G X hX N

/-- Every original normal head satisfies the concrete stability envelope:
one at degrees three/four, two at nine/eighteen, and floor(5w/27) elsewhere.
The original normal top image and all scalar induction steps are derived. -/
theorem transitiveTernaryHead_stability
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω] [Nonempty Ω]
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      ternaryStabilityBound (Nat.card Ω) := by
  apply transitiveTernaryHead_bound_with_finite_bypass
    ternaryStabilityBound (fun r => r / 3) ({18} : Finset ℕ)
    (degreeEighteen_stability_bypass h18)
    (primitiveTernary_stability_input hChief hPrimitive) hChief ?_ N
  intro r s hr hs hF
  exact ternaryStability_scalar r s hr hs (by simpa only [Finset.mem_singleton] using hF)

/-- The ordinary top bound required in the high-action induction. The
three small degree classes still require their finer actual-pair inputs. -/
theorem transitiveTernaryHead_stability_ordinary
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω] [Nonempty Ω]
    (N : Subgroup A) [N.Normal]
    (h3 : Nat.card Ω ≠ 3) (h4 : Nat.card Ω ≠ 4) (h9 : Nat.card Ω ≠ 9) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 5 * Nat.card Ω / 27 :=
  (transitiveTernaryHead_stability hChief hPrimitive h18 N).trans
    (ternaryStability_le_base _ h3 h4 h9)

end SymmetricSubgroupAsymptotics
