import SymmetricSubgroupAsymptotics.BinaryRegularEightTopEnumeration
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor

/-! Sparse certificates for the fixed-kernel and surviving-top factors
of the ORIGINAL regular K45 quotient centre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveCoordinateTemplate
open BinaryRegularEightNaturalRegistry

def fixedPredicate {c : ℕ} (C : BinaryCoordinateSpace 8 c) (v : V) : Prop :=
  v ∈ chart45.space ∧ ∀ t : H, rho t v - v ∈ C.space

def topPredicate {c : ℕ} (C : BinaryCoordinateSpace 8 c) (t : H) : Prop :=
  ∀ v, v ∈ chart45.space → rho t v - v ∈ C.space

theorem fixed_card_le {c d : ℕ} (C : BinaryCoordinateSpace 8 c)
    (D : BinaryCoordinateSpace 8 d)
    (hfixed : ∀ v, v ∈ D.space ↔ v ∈ chart45.space ∧
      ∀ j, rho (generators j) v - v ∈ C.space) :
    Nat.card {v : V // fixedPredicate C v} ≤ 2 ^ d := by
  let f : {v : V // fixedPredicate C v} → D.space := fun v =>
    ⟨v.val, (hfixed v.val).mpr ⟨v.property.1, fun j => v.property.2 (generators j)⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : D.space => (v : V)) h)
  exact (Nat.card_le_card_of_injective f hf).trans_eq D.card

theorem top_card_le {c : ℕ} (C : BinaryCoordinateSpace 8 c) (n : ℕ)
    (hc : Nat.card {i : Fin 8 // ∀ j : Fin 7,
      rho (groupElement i) (chart45.inclusion (Pi.single j 1)) -
        chart45.inclusion (Pi.single j 1) ∈ C.space} = n) :
    Nat.card {t : H // topPredicate C t} ≤ n := by
  let f : {t : H // topPredicate C t} → {i : Fin 8 // ∀ j : Fin 7,
      rho (groupElement i) (chart45.inclusion (Pi.single j 1)) -
        chart45.inclusion (Pi.single j 1) ∈ C.space} := fun t =>
    ⟨topRowEquiv.symm t.val, by
      intro j
      have he : groupElement (topRowEquiv.symm t.val) = t.val :=
        topRowEquiv.apply_symm_apply t.val
      rw [he]
      exact t.property _ ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply topRowEquiv.symm.injective
    exact congrArg (fun i : {i : Fin 8 // ∀ j : Fin 7,
      rho (groupElement i) (chart45.inclusion (Pi.single j 1)) -
        chart45.inclusion (Pi.single j 1) ∈ C.space} => i.val) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

end SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveCoordinateTemplate
