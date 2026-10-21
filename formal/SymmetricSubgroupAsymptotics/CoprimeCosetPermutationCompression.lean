import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Disjoint coset actions of two subgroups with coprime orders are jointly
faithful. Their degree is the sum of the indices, without a group model or
normality assumption on either subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CoprimeCosetPermutationCompression

variable {G : Type} [Group G] [Finite G]

def pairAction (H K : Subgroup G) :
    G →* Equiv.Perm (G ⧸ H) × Equiv.Perm (G ⧸ K) :=
  (MulAction.toPermHom G (G ⧸ H)).prod (MulAction.toPermHom G (G ⧸ K))

omit [Finite G] in
theorem pairAction_injective (H K : Subgroup G)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    Function.Injective (pairAction H K) := by
  apply (pairAction H K).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have he : pairAction H K g = 1 := hg
  have hH : g ∈ H.normalCore := by
    rw [H.normalCore_eq_ker]
    exact congrArg Prod.fst he
  have hK : g ∈ K.normalCore := by
    rw [K.normalCore_eq_ker]
    exact congrArg Prod.snd he
  have hm : g ∈ H ⊓ K := ⟨H.normalCore_le hH,K.normalCore_le hK⟩
  rwa [Subgroup.inf_eq_bot_of_coprime hcop] at hm

def action (H K : Subgroup G) : G →* Equiv.Perm (Fin (H.index + K.index)) :=
  let points : (G ⧸ H ⊕ G ⧸ K) ≃ Fin (H.index + K.index) :=
    Finite.equivFinOfCardEq (by rw [Nat.card_sum,←H.index_eq_card,←K.index_eq_card])
  points.permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (G ⧸ H) (G ⧸ K)).comp (pairAction H K))

theorem action_injective (H K : Subgroup G)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    Function.Injective (action H K) := by
  exact (Finite.equivFinOfCardEq
    (by rw [Nat.card_sum,←H.index_eq_card,←K.index_eq_card]) :
      (G ⧸ H ⊕ G ⧸ K) ≃ Fin (H.index + K.index)).permCongrHom.injective.comp
    (Equiv.Perm.sumCongrHom_injective.comp (pairAction_injective H K hcop))

set_option maxHeartbeats 600000 in
theorem order_six_or_ten_faithful_action
    (hG : Nat.card G = 6 ∨ Nat.card G = 10) :
    ∃ d : ℕ, 0 < d ∧
      (Nat.card G = 6 → d = 5) ∧ (Nat.card G = 10 → d = 7) ∧
      ∃ f : G →* Equiv.Perm (Fin d), Function.Injective f := by
  obtain ⟨q,hq,hcard⟩ : ∃ q : ℕ,(q = 3 ∨ q = 5) ∧ Nat.card G = 2*q := by
    rcases hG with h | h
    · exact ⟨3,Or.inl rfl,h⟩
    · exact ⟨5,Or.inr rfl,h⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  let Q : Sylow q G := Classical.choice inferInstance
  have hval2 : (2*q).factorization 2 = 1 := by
    rcases hq with rfl | rfl <;> decide +kernel
  have hvalq : (2*q).factorization q = 1 := by
    rcases hq with rfl | rfl <;> decide +kernel
  have hP : Nat.card P = 2 := by rw [P.card_eq_multiplicity,hcard,hval2,pow_one]
  have hQ : Nat.card Q = q := by rw [Q.card_eq_multiplicity,hcard,hvalq,pow_one]
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) := by
    rw [hP,hQ]
    rcases hq with rfl | rfl <;> decide
  have hiP : (P : Subgroup G).index = q := by
    have hm := (P : Subgroup G).card_mul_index
    rw [hP,hcard] at hm
    omega
  have hiQ : (Q : Subgroup G).index = 2 := by
    have hm := (Q : Subgroup G).card_mul_index
    rw [hQ,hcard] at hm
    have hp : 0 < q := by rcases hq with rfl | rfl <;> decide
    nlinarith
  refine ⟨(P : Subgroup G).index + (Q : Subgroup G).index,?_,?_,?_,
    action (P : Subgroup G) (Q : Subgroup G),
    action_injective (P : Subgroup G) (Q : Subgroup G) hcop⟩
  · rw [hiP,hiQ]
    omega
  · intro hsix
    rw [hiP,hiQ]
    have : q = 3 := by omega
    omega
  · intro hten
    rw [hiP,hiQ]
    have : q = 5 := by omega
    omega

end SymmetricSubgroupAsymptotics.CoprimeCosetPermutationCompression
