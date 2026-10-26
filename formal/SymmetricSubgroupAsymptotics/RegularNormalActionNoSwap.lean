import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import Mathlib.GroupTheory.Perm.Support

/-! A faithful action with a regular normal subgroup has no transposition
on at least five points. A commutator with a regular translation is the
product of two transpositions, hence fixes a point. Regularity forces
that commutator to be trivial. No primitivity or abelianness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RegularNormalActionNoSwap

private theorem exists_fixed_of_support_card_lt
    {X : Type} [Fintype X] [DecidableEq X] (f : Equiv.Perm X)
    (h : f.support.card < Fintype.card X) : ∃ x : X, f x = x := by
  by_contra hn
  have hall : f.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    exact Equiv.Perm.mem_support.mpr (fun hx => hn ⟨x, hx⟩)
  rw [hall, Finset.card_univ] at h
  exact (lt_irrefl _ h)

theorem not_isSwap
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)
    (hn : 5 ≤ Nat.card X) (g : G) :
    letI : Fintype X := Fintype.ofFinite X
    letI : DecidableEq X := Classical.decEq X
    ¬ (MulAction.toPermHom G X g).IsSwap := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  intro hs
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  have hs2 : (f g).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hs
  have hcomm (n : P.V) : g * (n : G) = (n : G) * g := by
    let u : G := g * (n : G) * g⁻¹ * (n : G)⁻¹
    have hu : u ∈ P.V := P.V.mul_mem
      ((inferInstance : P.V.Normal).conj_mem n n.property g) (P.V.inv_mem n.property)
    have he : f u = f g * (f n * (f g)⁻¹ * (f n)⁻¹) := by
      simp only [u, map_mul, map_inv]
      group
    have hsup : (f u).support.card ≤ 4 := by
      rw [he]
      calc
        _ ≤ ((f g).support ∪ (f n * (f g)⁻¹ * (f n)⁻¹).support).card :=
          Finset.card_le_card (Equiv.Perm.support_mul_le _ _)
        _ ≤ (f g).support.card + (f n * (f g)⁻¹ * (f n)⁻¹).support.card :=
          Finset.card_union_le _ _
        _ = 4 := by rw [Equiv.Perm.card_support_conj, Equiv.Perm.support_inv, hs2]
    obtain ⟨x, hx⟩ := exists_fixed_of_support_card_lt (f u)
      (by rw [← Nat.card_eq_fintype_card]; omega)
    have hu1 : u = 1 := congrArg Subtype.val
      (P.eq_one_of_smul_eq x (⟨u, hu⟩ : P.V) hx)
    calc
      g * (n : G) = u * (n : G) * g := by dsimp [u]; group
      _ = (n : G) * g := by rw [hu1, one_mul]
  obtain ⟨x, hx⟩ := exists_fixed_of_support_card_lt (f g)
    (by rw [hs2, ← Nat.card_eq_fintype_card]; omega)
  have hg1 : g = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨n, hny, _⟩ := P.regular x y
    calc
      g • y = g • (n • x) := by rw [hny]
      _ = (g * (n : G)) • x := (mul_smul _ _ _).symm
      _ = ((n : G) * g) • x := by rw [hcomm n]
      _ = (n : G) • (g • x) := mul_smul _ _ _
      _ = y := by rw [show g • x = x from hx]; exact hny
      _ = (1 : G) • y := (one_smul G y).symm
  have hh : (f g).support.card = 0 := by rw [hg1, map_one]; simp
  omega

end SymmetricSubgroupAsymptotics.RegularNormalActionNoSwap
