import SymmetricSubgroupAsymptotics.CommutingPairJointFixedDoubleCount
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Ring

/-! Splitting off zero in a genuine linear action leaves its actual
punctured action. When that action is transitive, the joint commuting
fixed-point count is |G| times the sum of the class counts of G and one
actual nonzero stabilizer. No capacity or orbit-count premise is hidden. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LinearPuncturedJointFixedCount
open AbelianActionClassBound CommutingPairJointFixedDoubleCount

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

@[reducible] def puncturedAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G {v : V // v ≠ 0} where
  smul g v := ⟨ρ g v.val, fun h => v.property ((ρ g).injective (h.trans (ρ g).map_zero.symm))⟩
  one_smul v := by
    apply Subtype.ext
    change ρ 1 v.val = v.val
    rw [ρ.map_one]
    rfl
  mul_smul g h v := by
    apply Subtype.ext
    change ρ (g * h) v.val = ρ g (ρ h v.val)
    rw [ρ.map_mul]
    rfl

def puncturedStabilizer (ρ : G →* (V ≃ₗ[K] V)) (v : {v : V // v ≠ 0}) : Subgroup G :=
  letI : MulAction G {v : V // v ≠ 0} := puncturedAction ρ
  MulAction.stabilizer G v

private def fixedPairSplit (ρ : G →* (V ≃ₗ[K] V)) (g h : G) :
    {v : V // ρ g v = v ∧ ρ h v = v} ≃
      Unit ⊕ {v : {v : V // v ≠ 0} // ρ g v.val = v.val ∧ ρ h v.val = v.val} where
  toFun v := if hv : v.val = 0 then Sum.inl ()
    else Sum.inr ⟨⟨v.val, hv⟩, v.property⟩
  invFun z := match z with
    | Sum.inl _ => ⟨0, (ρ g).map_zero, (ρ h).map_zero⟩
    | Sum.inr v => ⟨v.val.val, v.property⟩
  left_inv v := by
    dsimp
    split_ifs with hv
    · exact Subtype.ext hv.symm
    · rfl
  right_inv z := by
    rcases z with u | v
    · cases u
      simp
    · simp only [dif_neg v.val.property]

theorem joint_fixed_card_eq_of_punctured_transitive [Finite V] [Finite G]
    (ρ : G →* (V ≃ₗ[K] V))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, ρ g v = w)
    (v₀ : {v : V // v ≠ 0}) :
    Nat.card ((p : CommutingPairs G) ×
      {v : V // ρ p.val.1 v = v ∧ ρ p.val.2 v = v}) =
      Nat.card G * (Nat.card (ConjClasses G) +
        Nat.card (ConjClasses (puncturedStabilizer ρ v₀))) := by
  letI : Fintype (CommutingPairs G) := Fintype.ofFinite _
  letI : MulAction G {v : V // v ≠ 0} := puncturedAction ρ
  letI : MulAction.IsPretransitive G {v : V // v ≠ 0} := {
    exists_smul_eq := fun v w => by
      obtain ⟨g, hg⟩ := htrans v.val w.val v.property w.property
      exact ⟨g, Subtype.ext hg⟩ }
  have hpoint (p : CommutingPairs G) :
      Nat.card {v : V // ρ p.val.1 v = v ∧ ρ p.val.2 v = v} =
        1 + Nat.card {v : {v : V // v ≠ 0} //
          ρ p.val.1 v.val = v.val ∧ ρ p.val.2 v.val = v.val} := by
    rw [Nat.card_congr (fixedPairSplit ρ p.val.1 p.val.2), Nat.card_sum]
    simp
  let e : ((p : CommutingPairs G) × {v : {v : V // v ≠ 0} //
      ρ p.val.1 v.val = v.val ∧ ρ p.val.2 v.val = v.val}) ≃
      JointFixed (G := G) (X := {v : V // v ≠ 0}) := {
    toFun := fun z => ⟨z.1, ⟨z.2.val, Subtype.ext z.2.property.1, Subtype.ext z.2.property.2⟩⟩
    invFun := fun z => ⟨z.1, ⟨z.2.val,
      congrArg Subtype.val z.2.property.1, congrArg Subtype.val z.2.property.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hzero : (∑ _p : CommutingPairs G, (1 : ℕ)) = Nat.card (CommutingPairs G) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card, Nat.cast_id]
  have hnonzero : (∑ p : CommutingPairs G,
      Nat.card {v : {v : V // v ≠ 0} //
        ρ p.val.1 v.val = v.val ∧ ρ p.val.2 v.val = v.val}) =
      Nat.card (JointFixed (G := G) (X := {v : V // v ≠ 0})) :=
    Nat.card_sigma.symm.trans (Nat.card_congr e)
  calc
    _ = Nat.card (CommutingPairs G) +
        Nat.card (JointFixed (G := G) (X := {v : V // v ≠ 0})) := by
      rw [Nat.card_sigma]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, hzero, hnonzero]
    _ = _ := by
      rw [card_comm_eq_card_conjClasses_mul_card,
        joint_fixed_card_eq_of_pretransitive v₀]
      change Nat.card (ConjClasses G) * Nat.card G +
        Nat.card G * Nat.card (ConjClasses (puncturedStabilizer ρ v₀)) = _
      ring

end SymmetricSubgroupAsymptotics.LinearPuncturedJointFixedCount
