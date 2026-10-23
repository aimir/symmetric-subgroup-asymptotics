import SymmetricSubgroupAsymptotics.PGroupGeneratingCardinality
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Log

/-! Actual homomorphisms and automorphisms of a finite p-group are
determined on a generating set with at most log_p(|G|) entries. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PGroupAutomorphismCardinality

theorem monoidHom_card_le_pow_log (p : ℕ) [hp : Fact p.Prime]
    (G Q : Type*) [Group G] [Group Q] [Finite G] [Finite Q] (hG : IsPGroup p G) :
    Nat.card (G →* Q) ≤ (Nat.card Q)^Nat.log p (Nat.card G) := by
  obtain ⟨S,hS,hpow⟩ :=
    PGroupGeneratingCardinality.exists_generating_finset_prime_pow_le p G hG
  have hsize : S.card ≤ Nat.log p (Nat.card G) :=
    Nat.le_log_of_pow_le hp.out.one_lt hpow
  let f : (G →* Q) → (S → Q) := fun a s => a s.val
  have hf : Function.Injective f := by
    intro a b he
    apply MonoidHom.eq_of_eqOn_dense hS
    intro s hs
    exact congrFun he ⟨s,hs⟩
  calc
    Nat.card (G →* Q) ≤ Nat.card (S → Q) := Nat.card_le_card_of_injective f hf
    _ = (Nat.card Q)^S.card := by
      rw [Nat.card_fun,Nat.card_eq_fintype_card (α := S),Fintype.card_coe]
    _ ≤ (Nat.card Q)^Nat.log p (Nat.card G) := Nat.pow_le_pow_right Nat.card_pos hsize

theorem mulAut_card_le_pow_log (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G) :
    Nat.card (MulAut G) ≤ (Nat.card G)^Nat.log p (Nat.card G) := by
  letI : Finite (G →* G) := Finite.of_injective
    (fun f : G →* G => (f : G → G)) DFunLike.coe_injective
  have hAut : Nat.card (MulAut G) ≤ Nat.card (G →* G) :=
    Nat.card_le_card_of_injective (fun a : MulAut G => a.toMonoidHom)
      (fun _ _ he => MulEquiv.ext (fun g => DFunLike.congr_fun he g))
  exact hAut.trans (monoidHom_card_le_pow_log p G G hG)

end SymmetricSubgroupAsymptotics.PGroupAutomorphismCardinality
