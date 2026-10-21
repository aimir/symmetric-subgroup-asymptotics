import SymmetricSubgroupAsymptotics.BinaryHeisenbergTopCentralCore
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! Joint numerical envelopes for the original Heisenberg top. The
denominator axis is shared by every factor; arbitrary top-image normals
are distinguished from normals in the pair kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
open BinaryHeisenbergEightNaturalHeads

def rowEquiv : Fin 32 ≃ H :=
  Equiv.ofBijective BinaryEightOriginalRowActions.heisenbergRow
    BinaryEightOriginalRowActions.heisenbergRow_bijective

def fixedPredicate (K A : Submodule (ZMod 2) V) (v : V) : Prop :=
  v ∈ K ∧ ∀ t : H, rho t v - v ∈ A
def topPredicate (K A : Submodule (ZMod 2) V) (t : H) : Prop :=
  ∀ v, v ∈ K → rho t v - v ∈ A

theorem fixed_card_le {k c d : ℕ} (K : BinaryCoordinateSpace 8 k)
    (C : BinaryCoordinateSpace 8 c) (D : BinaryCoordinateSpace 8 d)
    (hf : ∀ v, v ∈ D.space ↔ v ∈ K.space ∧
      ∀ j, rho (generators j) v - v ∈ C.space) :
    Nat.card {v : V // fixedPredicate K.space C.space v} ≤ 2 ^ d :=
  BinaryCoordinateFixedTopCardBounds.fixed_card_le rho K C D generators hf

theorem top_card_le {k c : ℕ} (K : BinaryCoordinateSpace 8 k)
    (C : BinaryCoordinateSpace 8 c) (n : ℕ)
    (hc : Fintype.card {i : Fin 32 // ∀ j : Fin k,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (K.inclusion (Pi.single j 1)) -
        K.inclusion (Pi.single j 1) ∈ C.space} = n) :
    Nat.card {t : H // topPredicate K.space C.space t} ≤ n := by
  simpa only [true_and] using
    BinaryCoordinateFixedTopCardBounds.top_card_le rho K C rowEquiv (fun _ => True) n
      (by simpa only [Nat.card_eq_fintype_card, true_and] using hc)

theorem central_top_card_le {k c : ℕ} (K : BinaryCoordinateSpace 8 k)
    (C : BinaryCoordinateSpace 8 c) (n : ℕ)
    (hc : Fintype.card {i : Fin 32 //
      (BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
       BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i)
         BinaryHeisenbergTopCentralCore.z) ∧ ∀ j : Fin k,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (K.inclusion (Pi.single j 1)) -
        K.inclusion (Pi.single j 1) ∈ C.space} = n) :
    Nat.card {t : H // t ∈ Subgroup.center H ∧ topPredicate K.space C.space t} ≤ n := by
  let f : {t : H // t ∈ Subgroup.center H ∧ topPredicate K.space C.space t} →
      {i : Fin 32 //
      (BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
       BinaryHeisenbergTopCentralCore.PointEq (BinaryEightOriginalRowActions.heisenbergRow i)
         BinaryHeisenbergTopCentralCore.z) ∧ ∀ j : Fin k,
      rho (BinaryEightOriginalRowActions.heisenbergRow i) (K.inclusion (Pi.single j 1)) -
        K.inclusion (Pi.single j 1) ∈ C.space} := fun t =>
    ⟨rowEquiv.symm t.val, by
      have he : BinaryEightOriginalRowActions.heisenbergRow (rowEquiv.symm t.val) = t.val :=
        rowEquiv.apply_symm_apply t.val
      rw [he]
      constructor
      · rcases BinaryHeisenbergTopCentralCore.central_cases t.val t.property.1 with h | h
        · exact Or.inl (fun x => congrArg (fun g : H => g.val x) h)
        · exact Or.inr (fun x => congrArg (fun g : H => g.val x) h)
      · intro j
        exact t.property.2 _ ⟨_, rfl⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply rowEquiv.symm.injective
    exact congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective f hi).trans_eq
    (by rw [Nat.card_eq_fintype_card]; exact hc)

def JointAxisEnvelope (K R A : Submodule (ZMod 2) V) (originalDerived : ℕ) : Prop :=
  ∃ d z : ℕ,
    originalDerived ≤ Nat.card (A ⊓ R : Submodule (ZMod 2) V) * 2 ^ d ∧
    Nat.card {v : V // fixedPredicate K A v} *
      Nat.card {t : H // t ∈ Subgroup.center H ∧ topPredicate K A t} ≤
        Nat.card A * 2 ^ z ∧
    4 * d + 5 * z ≤ 32 ∧ z ≤ 4 ∧
    (R ≤ A ∨ ∃ zn : ℕ,
      Nat.card {v : V // fixedPredicate K A v} *
        Nat.card {t : H // topPredicate K A t} ≤ 2 * Nat.card A * 2 ^ zn ∧
      4 * d + 5 * zn ≤ 32 ∧ zn ≤ 4)

end SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
