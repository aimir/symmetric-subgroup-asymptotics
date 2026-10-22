import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Linarith

/-! A proper nontrivial subgroup of an actual simple group supplies a
proper conjugacy stabilizer. A strict weighted conjugacy-family count
and a genuine order lower bound then imply the index-square inequality. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGSimpleConjugateFamilyIndex
open PrimitiveSocleRawStructure
variable {G : Type} [Group G] [IsSimpleGroup G]

theorem least_index_le_family (R : Subgroup G) (hR0 : R ≠ ⊥) (hR1 : R ≠ ⊤)
    (ell : ℕ) (hell : LeastProperIndex G ell) :
    ell ≤ Nat.card (Set.range (fun g : G => R.map (MulAut.conj g).toMonoidHom)) := by
  letI : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  let S := MulAction.stabilizer G R
  have hS : S ≠ ⊤ := by
    intro hs
    have hnormal : R.Normal := {
      conj_mem := by
        intro x hx g
        have hg : g ∈ S := by rw [hs]; exact Subgroup.mem_top g
        have he : R.map (MulAut.conj g).toMonoidHom = R := hg
        rw [← he]
        exact ⟨x, hx, rfl⟩ }
    exact hnormal.eq_bot_or_eq_top.elim hR0 hR1
  have horbit : MulAction.orbit G R =
      Set.range (fun g : G => R.map (MulAut.conj g).toMonoidHom) := by
    ext T
    rw [MulAction.mem_orbit_iff]
    rfl
  calc
    ell ≤ S.index := hell.2 S hS
    _ = _ := by
      change (MulAction.stabilizer G R).index = _
      rw [MulAction.index_stabilizer, horbit, Nat.card_coe_set_eq]

theorem square_lt_of_weighted_family (q N c R M B : ℕ)
    (hq : 0 < q) (hR : R < q ^ c) (hM : M * q ^ c ≤ R * q ^ N)
    (hB : q ^ (2 * N) ≤ B) : M ^ 2 < B := by
  have hqc : 0 < q ^ c := pow_pos hq c
  have hqN : 0 < q ^ N := pow_pos hq N
  have hr := Nat.mul_lt_mul_of_pos_right hR hqN
  have hlt : M < q ^ N := by nlinarith
  have hs : M ^ 2 < (q ^ N) ^ 2 := by nlinarith
  rw [← pow_mul, Nat.mul_comm N 2] at hs
  exact hs.trans_le hB

end SymmetricSubgroupAsymptotics.CFSGSimpleConjugateFamilyIndex
