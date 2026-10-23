import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergOrbitSums
import SymmetricSubgroupAsymptotics.CFSGScaledConstantFixedDegree
import SymmetricSubgroupAsymptotics.CFSGCentralMovingPart

/-! The Heisenberg lower degree on an ACTUAL action of the original
radical. Constant central nonidentity fixed counts are the remaining
geometric input, to be supplied by literal norm-torus conjugacy. The
proof removes centre-fixed points and uses exact orbit divisibility. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open MulAction

instance radicalCentre_normal (q : CFSG.PrimePower) (s : ℕ) : (radicalCentre q s).Normal := by
  change (fixedRadicalParameterHom q s).ker.Normal
  infer_instance

theorem radical_degree_lower_of_constant_central_fixedBy {X : Type*}
    (q : CFSG.PrimePower) (s : ℕ) [MulAction (fixedRadical q s) X] [Finite X]
    (f : ℕ)
    (hfix : ∀ c : radicalCentre q s, c ≠ 1 → Nat.card (fixedBy X c) = f)
    (hmove : ∃ (c : radicalCentre q s) (x : X), c • x ≠ x) :
    q.order ^ (s + 2) ≤ Nat.card X := by
  let Y := CFSGCentralMovingPart.MovingPart (radicalCentre q s) X
  have hnone : ∀ y : Y, ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) y :=
    CFSGCentralMovingPart.movingPart_no_whole_stabilizer (radicalCentre q s)
  let f' := f - Nat.card (CFSGCentralMovingPart.FixedPart (radicalCentre q s) X)
  have hfix' : ∀ c : radicalCentre q s, c ≠ 1 → Nat.card (fixedBy Y c) = f' :=
    CFSGCentralMovingPart.constant_fixedBy_movingPart (radicalCentre q s) f hfix
  have hmove' : ∃ (c : radicalCentre q s) (y : Y), c • y ≠ y :=
    CFSGCentralMovingPart.exists_move_movingPart (radicalCentre q s) hmove
  obtain ⟨c, y, hcy⟩ := hmove'
  have hc : c ≠ 1 := by
    rintro rfl
    exact hcy (one_smul (radicalCentre q s) y)
  have hfixed : q.order ^ (s + 1) ∣ f' := by
    rw [← hfix' c hc]
    exact radical_moving_fixedBy_divisibility q s hnone c
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos q.exponent
  have hh := CFSGConjugateSubgroupDegree.scaled_card_le_of_constant_fixedBy
    (P := radicalCentre q s) (X := Y) (q.order ^ (s + 1)) f' (pow_pos hq _)
    hfix' ⟨c, y, hcy⟩ (radical_moving_degree_divisibility q s hnone) hfixed
    (radical_moving_orbit_divisibility q s hnone)
  rw [radicalCentre_card, ← pow_succ] at hh
  have hY : q.order ^ (s + 2) ≤ Nat.card Y := by
    simpa only [Nat.add_assoc] using hh
  exact hY.trans (CFSGCentralMovingPart.movingPart_card_le (radicalCentre q s))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
