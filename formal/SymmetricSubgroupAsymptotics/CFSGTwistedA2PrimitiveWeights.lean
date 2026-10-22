import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusAction
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots
import Mathlib.Tactic.Linarith

/-! A literal primitive quadratic-extension unit gives two nontrivial
torus layer weights for every admissible rank-two parameter q>=3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

theorem exists_nontrivial_layer_weights (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ∃ z : q.Extension 2, z ≠ 0 ∧
      firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z ≠ 1 ∧
      centralWeight (q.Extension 2) (definingFieldAutomorphism q 2) z ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (q.Extension 2)ˣ)
  have hsq : q.order ^ 2 - 1 + 1 = q.order ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hsub : q.order - 2 + 2 = q.order := Nat.sub_add_cancel (by omega)
  have hsmall (m : ℕ) (hm : 0 < m) (hlt : m < q.order ^ 2 - 1) :
      (g : q.Extension 2) ^ m ≠ 1 := by
    intro h
    have hu : g ^ m = 1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h)
    have hd := orderOf_dvd_of_pow_eq_one hu
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, extension_two_card] at hd
    exact (Nat.le_of_dvd hm hd).not_gt hlt
  refine ⟨g, Units.ne_zero g, ?_, ?_⟩
  · intro h
    change (g : q.Extension 2) ^ 2 / (g : q.Extension 2) ^ q.order = 1 at h
    have he : (g : q.Extension 2) ^ 2 = (g : q.Extension 2) ^ q.order :=
      (div_eq_one_iff_eq (pow_ne_zero _ (Units.ne_zero g))).mp h
    apply hsmall (q.order - 2) (by omega) (by nlinarith)
    rw [pow_sub₀ _ (Units.ne_zero g) (by omega), ← he,
      mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero g))]
  · intro h
    change (g : q.Extension 2) * (g : q.Extension 2) ^ q.order = 1 at h
    apply hsmall (q.order + 1) (by omega) (by nlinarith)
    simpa only [pow_succ, mul_comm] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedA2DiagonalTorus
