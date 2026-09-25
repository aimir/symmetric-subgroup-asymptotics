import SymmetricSubgroupAsymptotics.CriticalActions
import SymmetricSubgroupAsymptotics.LabelledOrbitProfiles
import SymmetricSubgroupAsymptotics.QuadraticRealization

/-! Four concrete colours and their original quadratic quotient charts. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The four genuinely distinct critical action colours. -/
inductive CriticalActionKind
  | c2 | v4 | d8 | e8
  deriving DecidableEq, Fintype

/-- Literal point sets of the four faithful actions. -/
def criticalActionPoints : CriticalActionKind → Type
  | .c2 => Fin 1 → ZMod 2
  | .v4 => Fin 2 → ZMod 2
  | .d8 => (Fin 1 → ZMod 2) × ZMod 2
  | .e8 => (Fin 2 → ZMod 2) × ZMod 2

instance (i : CriticalActionKind) : Fintype (criticalActionPoints i) := by
  cases i <;> dsimp [criticalActionPoints] <;> infer_instance

instance (i : CriticalActionKind) : DecidableEq (criticalActionPoints i) := by
  cases i <;> dsimp [criticalActionPoints] <;> infer_instance

instance (i : CriticalActionKind) : Nonempty (criticalActionPoints i) := by
  cases i <;> dsimp [criticalActionPoints] <;> infer_instance

/-- The actual subgroups of the four original symmetric groups. -/
def criticalActionSubgroup : (i : CriticalActionKind) → Subgroup (Equiv.Perm (criticalActionPoints i))
  | .c2 => regularBinaryPermutationGroup 1
  | .v4 => regularBinaryPermutationGroup 2
  | .d8 => heisenbergPermutationGroup 1
  | .e8 => heisenbergPermutationGroup 2

def criticalActionDegree : CriticalActionKind → ℕ
  | .c2 => 2 | .v4 => 4 | .d8 => 4 | .e8 => 8

def criticalActionOrder : CriticalActionKind → ℕ
  | .c2 => 2 | .v4 => 4 | .d8 => 8 | .e8 => 32

def criticalActionNormalizerOrder : CriticalActionKind → ℕ
  | .c2 => 2 | .v4 => 24 | .d8 => 8 | .e8 => 384

theorem criticalAction_point_card (i : CriticalActionKind) :
    Fintype.card (criticalActionPoints i) = criticalActionDegree i := by
  cases i
  · change Fintype.card (Fin 1 → ZMod 2) = 2
    norm_num
  · change Fintype.card (Fin 2 → ZMod 2) = 4
    norm_num
  · change Fintype.card ((Fin 1 → ZMod 2) × ZMod 2) = 4
    norm_num
  · change Fintype.card ((Fin 2 → ZMod 2) × ZMod 2) = 8
    norm_num

theorem criticalAction_group_card (i : CriticalActionKind) :
    Nat.card (criticalActionSubgroup i) = criticalActionOrder i := by
  cases i
  · exact regularBinaryPermutationGroup_card 1
  · exact regularBinaryPermutationGroup_card 2
  · exact heisenbergPermutationGroup_card 1
  · exact heisenbergPermutationGroup_card 2

theorem criticalAction_normalizer_card (i : CriticalActionKind) :
    Nat.card (Subgroup.normalizer
      (criticalActionSubgroup i : Set (Equiv.Perm (criticalActionPoints i)))) =
      criticalActionNormalizerOrder i := by
  cases i
  · exact c2_normalizer_card
  · exact v4_normalizer_card
  · exact d8_normalizer_card
  · exact e8_normalizer_card

private theorem range_action_transitive {G Ω : Type*} [Group G]
    (ρ : G →* Equiv.Perm Ω) (h : ∀ x y : Ω, ∃ g, ρ g x = y) (x y : Ω) :
    ∃ g : ρ.range, (g : Equiv.Perm Ω) x = y := by
  obtain ⟨g, hg⟩ := h x y
  exact ⟨⟨ρ g, ⟨g, rfl⟩⟩, hg⟩

theorem criticalAction_transitive (i : CriticalActionKind) (x y : criticalActionPoints i) :
    ∃ g : criticalActionSubgroup i, (g : Equiv.Perm (criticalActionPoints i)) x = y := by
  cases i
  · exact range_action_transitive _ regularBinaryAction_transitive x y
  · exact range_action_transitive _ regularBinaryAction_transitive x y
  · exact range_action_transitive _ BinaryHeisenberg.action_transitive x y
  · exact range_action_transitive _ BinaryHeisenberg.action_transitive x y

/-- Equality of transported action groups forces equality of colours,
including the two different degree-four actions. -/
theorem criticalAction_types_separated :
    OrbitActionTypesSeparated criticalActionPoints criticalActionSubgroup := by
  intro i l e hi hl
  have hle : Nat.card (criticalActionSubgroup i) ≤ Nat.card (criticalActionSubgroup l) := by
    apply Nat.card_le_card_of_injective
      (fun u : criticalActionSubgroup i =>
        (⟨e.permCongr u.1, hi u.1 u.2⟩ : criticalActionSubgroup l))
    intro u v h
    exact Subtype.ext (e.permCongr.injective (congrArg Subtype.val h))
  have hge : Nat.card (criticalActionSubgroup l) ≤ Nat.card (criticalActionSubgroup i) := by
    apply Nat.card_le_card_of_injective
      (fun u : criticalActionSubgroup l =>
        (⟨e.symm.permCongr u.1, hl u.1 u.2⟩ : criticalActionSubgroup i))
    intro u v h
    exact Subtype.ext (e.symm.permCongr.injective (congrArg Subtype.val h))
  have hcard : criticalActionOrder i = criticalActionOrder l := by
    rw [← criticalAction_group_card i, ← criticalAction_group_card l]
    exact Nat.le_antisymm hle hge
  cases i <;> cases l <;> first | rfl | norm_num [criticalActionOrder] at hcard

/-- The literal D8 quotient coordinates interleaved as `(a0,b0)`. -/
def d8QuotientChart :
    ((Fin 1 → ZMod 2) × (Fin 1 → ZMod 2)) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v.1 0, v.2 0]
  invFun x := (fun _ => x 0, fun _ => x 1)
  left_inv v := by ext i <;> fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

/-- The literal E8 quotient coordinates interleaved as `(a0,b0,a1,b1)`. -/
def e8QuotientChart :
    ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun v := ![v.1 0, v.2 0, v.1 1, v.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv v := by ext i <;> fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

/-- The D8 square form is exactly the already-counted hyperbolic form. -/
theorem d8QuotientChart_quadratic (v : (Fin 1 → ZMod 2) × (Fin 1 → ZMod 2)) :
    hyperbolicQuadraticTwo (d8QuotientChart v) = binaryDot v.2 v.1 := by
  simp [d8QuotientChart, binaryDot, mul_comm]

/-- The E8 square form is exactly the already-counted four-dimensional form. -/
theorem e8QuotientChart_quadratic (v : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    hyperbolicQuadraticFour (e8QuotientChart v) = binaryDot v.2 v.1 := by
  simp [e8QuotientChart, binaryDot, Fin.sum_univ_two, mul_comm]

/-- Equality with the original retained square coordinate, not merely an
isometry between unnamed forms. -/
theorem d8_square_coordinate (g : BinaryHeisenberg 1) :
    binarySquareCoordinate (BinaryHeisenberg.quotient 1) (BinaryHeisenberg.kernelChart 1) g =
      hyperbolicQuadraticTwo (d8QuotientChart (g.a, g.b)) := by
  rw [d8QuotientChart_quadratic]
  change (g ^ 2).c = binaryDot g.b g.a
  rw [BinaryHeisenberg.square]
  rfl

theorem e8_square_coordinate (g : BinaryHeisenberg 2) :
    binarySquareCoordinate (BinaryHeisenberg.quotient 2) (BinaryHeisenberg.kernelChart 2) g =
      hyperbolicQuadraticFour (e8QuotientChart (g.a, g.b)) := by
  rw [e8QuotientChart_quadratic]
  change (g ^ 2).c = binaryDot g.b g.a
  rw [BinaryHeisenberg.square]
  rfl

end SymmetricSubgroupAsymptotics
