import SymmetricSubgroupAsymptotics.BilinearPairFixerRestriction
import SymmetricSubgroupAsymptotics.QuadraticPolarAffineFibreCardinality
import SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticLevelProjectiveBound
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Count actual quadratic isometries by the two actual point orbits
of a polar pair and its actual pointwise fixer. The ambient quadratic
form may have a radical. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.QuadraticIsometryPairOrbitCardinality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def isometries (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {e | ∀ v : V, Q (e v) = Q v}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro e f he hf v
    exact (he (f v)).trans (hf v)
  inv_mem' := by
    intro e he v
    have h := he (e.symm v)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem preserves_polar (Q : QuadraticForm K V) (e : isometries Q) (x y : V) :
    Q.polarBilin (e.val x) (e.val y) = Q.polarBilin x y := by
  change Q (e.val x + e.val y) - Q (e.val x) - Q (e.val y) =
    Q (x + y) - Q x - Q y
  rw [← e.val.map_add, e.property, e.property, e.property]

/-- A nonzero polar pairing yields a nonzero quadratic value on one
of the two vectors or their sum; no quadratic-form classification is used. -/
theorem exists_nonzero_level_pair [CharP K 2] (Q : QuadraticForm K V)
    (x y : V) (hxy : Q.polarBilin x y = 1) :
    ∃ u w : V, Q u ≠ 0 ∧ Q.polarBilin u w = 1 := by
  have hself (v : V) : Q.polarBilin v v = 0 := by
    change QuadraticMap.polar Q v v = 0
    rw [QuadraticMap.polar_self]
    exact CharTwo.two_nsmul _
  have hyx : Q.polarBilin y x = 1 := by
    change QuadraticMap.polar Q y x = 1
    rw [QuadraticMap.polar_comm]
    exact hxy
  by_cases hx : Q x ≠ 0
  · exact ⟨x, y, hx, hxy⟩
  by_cases hy : Q y ≠ 0
  · exact ⟨y, x, hy, hyx⟩
  have hx0 : Q x = 0 := not_ne_iff.mp hx
  have hy0 : Q y = 0 := not_ne_iff.mp hy
  have hsum : Q (x + y) = 1 := by
    have hp : Q (x + y) - Q x - Q y = 1 := hxy
    simpa only [hx0, hy0, sub_zero] using hp
  refine ⟨x + y, x, ?_, ?_⟩
  · rw [hsum]
    exact one_ne_zero
  · rw [map_add, LinearMap.add_apply, hself, hyx, zero_add]

/-- The complement factor is exactly the full linear group of the actual
common kernel, rather than an independently chosen stabilizer. -/
theorem card_le_projective_mul_polar_fibre_mul_complement
    [Finite K] [Finite V] [CharP K 2]
    (Q : QuadraticForm K V) (u w : V) (hu : Q u ≠ 0)
    (huw : Q.polarBilin u w = 1) :
    Nat.card (isometries Q) ≤
      Nat.card (ℙ K V) * (2 * Nat.card K ^ (Module.finrank K V - 2)) *
        Nat.card (BilinearPairFixerRestriction.complement Q.polarBilin u w ≃ₗ[K]
          BilinearPairFixerRestriction.complement Q.polarBilin u w) := by
  letI : Finite (V ≃ₗ[K] V) := Finite.of_injective
    (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  let O := isometries Q
  let S := MulAction.stabilizer O u
  let T := MulAction.stabilizer S w
  have hzero (v : V) : Q.polarBilin v v = 0 := by
    change QuadraticMap.polar Q v v = 0
    rw [QuadraticMap.polar_self]
    exact CharTwo.two_nsmul _
  have hwu : Q.polarBilin w u = 1 := by
    change QuadraticMap.polar Q w u = 1
    rw [QuadraticMap.polar_comm]
    exact huw
  let first : MulAction.orbit O u → {v : V // Q v = Q u} := fun y =>
    ⟨y.val, by
      obtain ⟨g, hg⟩ := y.property
      change g.val u = y.val at hg
      rw [← hg]
      exact g.property u⟩
  have hfirstinj : Function.Injective first := by
    intro y z he
    exact Subtype.ext (congrArg (fun x : {v : V // Q v = Q u} => x.val) he)
  have hfirst : Nat.card (MulAction.orbit O u) ≤ Nat.card (ℙ K V) :=
    (Nat.card_le_card_of_injective first hfirstinj).trans
      (CharacteristicTwoQuadraticLevelProjectiveBound.level_card_le_projective_card
        Q (map_zero Q) (fun a v => by
          simpa only [smul_eq_mul, pow_two] using Q.map_smul a v) (Q u) hu)
  let second : MulAction.orbit S w →
      {v : V // Q.polarBilin u v = 1 ∧ Q v = Q w} := fun y =>
    ⟨y.val, by
      obtain ⟨g, hg⟩ := y.property
      change g.val.val w = y.val at hg
      rw [← hg]
      have hgfix : g.val.val u = u := g.property
      refine ⟨?_, g.val.property w⟩
      calc
        _ = Q.polarBilin (g.val.val u) (g.val.val w) :=
          congrArg (fun z => Q.polarBilin z (g.val.val w)) hgfix.symm
        _ = Q.polarBilin u w := preserves_polar Q g.val u w
        _ = 1 := huw⟩
  have hsecondinj : Function.Injective second := by
    intro y z he
    exact Subtype.ext (congrArg
      (fun x : {v : V // Q.polarBilin u v = 1 ∧ Q v = Q w} => x.val) he)
  have hsecond : Nat.card (MulAction.orbit S w) ≤
      2 * Nat.card K ^ (Module.finrank K V - 2) :=
    (Nat.card_le_card_of_injective second hsecondinj).trans
      (QuadraticPolarAffineFibreCardinality.polar_affine_level_card_le Q u w hu huw (Q w))
  let fixer : T → BilinearPairFixerRestriction.Fixer Q.polarBilin u w := fun g =>
    ⟨g.val.val.val, preserves_polar Q g.val.val, g.val.property, g.property⟩
  have hfixerinj : Function.Injective fixer := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : BilinearPairFixerRestriction.Fixer Q.polarBilin u w => x.val) he
  have hfixer := (Nat.card_le_card_of_injective fixer hfixerinj).trans
    (BilinearPairFixerRestriction.fixer_card_le Q.polarBilin u w
      (hzero u) (hzero w) huw hwu)
  have hO : Nat.card O = Nat.card (MulAction.orbit O u) * Nat.card S := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup O u)).symm
  have hS : Nat.card S = Nat.card (MulAction.orbit S w) * Nat.card T := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S w)).symm
  change Nat.card O ≤ _
  rw [hO, hS]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul hfirst (Nat.mul_le_mul hsecond hfixer)

end SymmetricSubgroupAsymptotics.QuadraticIsometryPairOrbitCardinality
