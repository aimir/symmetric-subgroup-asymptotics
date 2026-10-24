import SymmetricSubgroupAsymptotics.BinaryQuadraticLevelCardinality
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! Actual quadratic levels on a nonzero polar affine hyperplane.
The free line direction is the actual vector u with Q(u)!=0; each
line has at most two level points. Two genuine linear-functional
kernels identify the remaining cardinal as q^(dim V-2). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.QuadraticPolarAffineFibreCardinality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem affine_line_formula (Q : QuadraticForm K V) (u w : V) (s : K) :
    Q (w + s • u) = Q u * s ^ 2 + Q.polarBilin w u * s + Q w := by
  have h : Q (w + s • u) - Q w - Q (s • u) = s * Q.polarBilin w u := by
    change QuadraticMap.polar Q w (s • u) = s * QuadraticMap.polar Q w u
    simpa only [smul_eq_mul] using (QuadraticMap.polar_smul_right Q s w u)
  calc
    _ = (s * Q.polarBilin w u + Q (s • u)) + Q w :=
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp h)
    _ = _ := by rw [Q.map_smul]; simp only [smul_eq_mul]; ring

theorem affine_line_level_card_le_two (Q : QuadraticForm K V) (u w : V)
    (c : K) (hu : Q u ≠ 0) : Nat.card {s : K // Q (w + s • u) = c} ≤ 2 := by
  let e : {s : K // Q (w + s • u) = c} ≃
      {s : K // Q u * s ^ 2 + Q.polarBilin w u * s + Q w = c} := {
    toFun := fun s => ⟨s.val, (affine_line_formula Q u w s.val).symm.trans s.property⟩
    invFun := fun s => ⟨s.val, (affine_line_formula Q u w s.val).trans s.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).le.trans
    (BinaryQuadraticLevelCardinality.quadratic_fibre_card_le_two
      (Q u) (Q.polarBilin w u) (Q w) c hu)

/-- The actual polar hyperplane, not a supplied coordinate census.
The vector w certifies that the polar functional is nonzero. -/
theorem polar_affine_level_card_le [Finite K] [Finite V] [CharP K 2]
    (Q : QuadraticForm K V) (u w : V) (hu : Q u ≠ 0)
    (hw : Q.polarBilin u w = 1) (c : K) :
    Nat.card {v : V // Q.polarBilin u v = 1 ∧ Q v = c} ≤
      2 * Nat.card K ^ (Module.finrank K V - 2) := by
  letI : Module.Finite K V := Module.Finite.of_finite
  let L : Module.Dual K V := Q.polarBilin u
  have hwL : L w = 1 := hw
  let W := L.ker
  have hLne : L ≠ 0 := by
    intro he
    have hz : L w = 0 := by rw [he, LinearMap.zero_apply]
    exact zero_ne_one (hz.symm.trans hwL)
  have hself : L u = 0 := by
    change QuadraticMap.polar Q u u = 0
    rw [QuadraticMap.polar_self]
    exact CharTwo.two_nsmul _
  let uW : W := ⟨u, hself⟩
  have huW : uW ≠ 0 := by
    intro he
    have hz : u = 0 := congrArg (fun v : W => (v : V)) he
    exact hu (by rw [hz, map_zero])
  obtain ⟨g, hgu⟩ := Module.Projective.exists_dual_eq_one K huW
  have hgne : g ≠ 0 := by
    intro he
    have hz : g uW = 0 := by rw [he, LinearMap.zero_apply]
    exact zero_ne_one (hz.symm.trans hgu)
  have hdL : Module.finrank K W + 1 = Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hLne
  have hdg : Module.finrank K g.ker + 1 = Module.finrank K W :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hgne
  have hd : Module.finrank K g.ker = Module.finrank K V - 2 := by omega
  have hcard : Nat.card g.ker = Nat.card K ^ (Module.finrank K V - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := g.ker), hd]
  let A := {v : V // L v = 1 ∧ Q v = c}
  let code : A → Σ r : g.ker, {s : K // Q (w + (r.val : V) + s • u) = c} := fun v => by
    let k : W := ⟨v.val - w, by
      change L (v.val - w) = 0
      rw [map_sub, v.property.1, hwL, sub_self]⟩
    let a := g k
    let r : g.ker := ⟨k - a • uW, by
      change g (k - a • uW) = 0
      rw [map_sub, map_smul, hgu, smul_eq_mul, mul_one, sub_self]⟩
    refine ⟨r, ⟨a, ?_⟩⟩
    have he : w + (r.val : V) + a • u = v.val := by
      change w + ((v.val - w) - a • u) + a • u = v.val
      abel
    rw [he]
    exact v.property.2
  have hrec (v : A) : w + ((code v).1.val : V) + (code v).2.val • u = v.val := by
    dsimp only [code]
    change w + ((v.val - w) - _ • u) + _ • u = v.val
    abel
  have hcode : Function.Injective code := by
    intro v z he
    have hr : (code v).1 = (code z).1 := congrArg Sigma.fst he
    have hs : (code v).2.val = (code z).2.val := congrArg
      (fun x : Σ r : g.ker, {s : K // Q (w + (r.val : V) + s • u) = c} => x.2.val) he
    apply Subtype.ext
    calc
      v.val = w + ((code v).1.val : V) + (code v).2.val • u := (hrec v).symm
      _ = w + ((code z).1.val : V) + (code z).2.val • u :=
        congrArg₂ (fun (r : V) (a : K) => w + r + a • u)
          (congrArg (fun r : g.ker => (r.val : V)) hr) hs
      _ = z.val := hrec z
  letI : Fintype g.ker := Fintype.ofFinite _
  change Nat.card A ≤ _
  calc
    _ ≤ Nat.card (Σ r : g.ker, {s : K // Q (w + (r.val : V) + s • u) = c}) :=
      Nat.card_le_card_of_injective code hcode
    _ = ∑ r : g.ker, Nat.card {s : K // Q (w + (r.val : V) + s • u) = c} := Nat.card_sigma
    _ ≤ ∑ _r : g.ker, 2 := Finset.sum_le_sum (fun r _ =>
      affine_line_level_card_le_two Q u (w + (r.val : V)) c hu)
    _ = 2 * Nat.card g.ker := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Nat.cast_id, Nat.mul_comm]
    _ = 2 * Nat.card K ^ (Module.finrank K V - 2) := congrArg (fun n : ℕ => 2 * n) hcard

end SymmetricSubgroupAsymptotics.QuadraticPolarAffineFibreCardinality
