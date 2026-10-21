import SymmetricSubgroupAsymptotics.CentralBinaryPairFrameExists
import SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates

/-! Every original finite transitive binary action has a central-pair
coordinate tower. Selected tower elements retain arbitrary higher-bit
errors; this asserts no pure translations or regular elementary subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem transitive_binary_triangular_coordinates_exists
    {X : Type} [Finite X] (n : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U) (hdegree : Nat.card X = 2^n) :
    Nonempty (BinaryTriangularPointCoordinates U X n) := by
  suffices h : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = 2^n →
      Nonempty (BinaryTriangularPointCoordinates U X n) from h n X U hU hdegree
  intro n
  induction n with
  | zero =>
    intro X _ U _ _ hdegree
    letI : Fintype X := Fintype.ofFinite X
    let e : X ≃ (Fin 0 → ZMod 2) := Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, hdegree]
      simp)
    exact ⟨⟨e, (fun _ i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩⟩
  | succ n ih =>
    intro X _ U _ hU hdegree
    obtain ⟨F, z, hz⟩ := transitive_central_binary_pair_frame_exists n U hU hdegree
    letI : MulAction.IsPretransitive F.top.range (Fin (2^n)) := F.top_pretransitive
    obtain ⟨T⟩ := ih (Fin (2^n)) F.top.range (F.top_isPGroup hU) (by simp only [Nat.card_fin])
    exact ⟨BinaryTriangularPointCoordinates.ofPairFrame F T z hz⟩

end SymmetricSubgroupAsymptotics
