import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Ring

/-! A uniform bound on nonidentity centralizers bounds the classes of
every actual subgroup. The identity fibre is counted separately; no
monotonicity of conjugacy-class counts under subgroup inclusion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CentralizerClassBound

variable {G : Type*} [Group G] [Finite G]

def commutingEquiv : {p : G×G // Commute p.1 p.2} ≃
    (g : G) × {h : G // Commute g h} where
  toFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem class_card_mul_le (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c) :
    Nat.card G*Nat.card (ConjClasses G) ≤ Nat.card G+(Nat.card G-1)*c := by
  letI : Fintype G := Fintype.ofFinite _
  have hone : Nat.card {h : G // Commute (1 : G) h} = Nat.card G := by
    apply Nat.card_congr
    exact { toFun := Subtype.val
            invFun := fun g => ⟨g,Commute.one_left g⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  have hrest : (∑ g ∈ (Finset.univ : Finset G).erase 1,
      Nat.card {h : G // Commute g h}) ≤ (Nat.card G-1)*c := by
    calc
      _ ≤ ∑ _g ∈ (Finset.univ : Finset G).erase 1, c := by
        apply Finset.sum_le_sum
        intro g hg
        exact hc g (Finset.mem_erase.mp hg).1
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
          Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  have he := Nat.card_congr (commutingEquiv (G := G))
  rw [card_comm_eq_card_conjClasses_mul_card,Nat.card_sigma,
    ← Finset.add_sum_erase (Finset.univ : Finset G)
      (fun g => Nat.card {h : G // Commute g h}) (Finset.mem_univ (1 : G)),hone] at he
  rw [Nat.mul_comm] at he
  exact he.le.trans (Nat.add_le_add_left hrest _)

theorem class_card_le (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c) :
    Nat.card (ConjClasses G) ≤ c+1 := by
  have h := class_card_mul_le c hc
  have hbound : Nat.card G*Nat.card (ConjClasses G) ≤ Nat.card G*(c+1) := by
    calc
      _ ≤ Nat.card G+(Nat.card G-1)*c := h
      _ ≤ Nat.card G+Nat.card G*c :=
        Nat.add_le_add_left (Nat.mul_le_mul_right c (Nat.sub_le _ _)) _
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := G))

theorem class_card_le_of_injective {A : Type*} [Group A] [Finite A]
    (f : A →* G) (hf : Function.Injective f) (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c) :
    Nat.card (ConjClasses A) ≤ c+1 := by
  apply class_card_le c
  intro a ha
  have hfa : f a ≠ 1 := by
    intro he
    exact ha (hf (he.trans (map_one f).symm))
  apply le_trans ?_ (hc (f a) hfa)
  apply Nat.card_le_card_of_injective
    (fun h : {h : A // Commute a h} =>
      (⟨f h.val,by
        have he := congrArg f h.property
        simpa only [map_mul] using he⟩ : {h : G // Commute (f a) h}))
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

theorem subgroup_class_card_le (c : ℕ)
    (hc : ∀ g : G, g≠1 → Nat.card {h : G // Commute g h} ≤ c)
    (H : Subgroup G) : Nat.card (ConjClasses H) ≤ c+1 :=
  class_card_le_of_injective H.subtype Subtype.val_injective c hc

end SymmetricSubgroupAsymptotics.CentralizerClassBound
