import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootCover
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-! An explicit index for the actual positive D4 lattice roots. The
equivalence uses the proved energy bound and root cover, rather than an
assumed census. Heights distinguish the successive fixed-upper layers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
open CFSGNormTwoRootPairing CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4PositiveRootCover

abbrev OrbitIndex := Fin 3 ⊕ (Fin 3 × Fin 3)
abbrev Positive := {k : Roots (CartanMatrix.D 4) // ∀ i, 0 ≤ k.val i}

def coordinates : OrbitIndex → Fin 4 → ℤ
  | Sum.inl s => longCoordinates s
  | Sum.inr p => shortCoordinates p.1 p.2

theorem coordinates_injective : Function.Injective coordinates := by decide

def positiveRoot : OrbitIndex → Positive
  | Sum.inl s => ⟨longRoot s, long_positive s⟩
  | Sum.inr p => ⟨shortRoot p.1 p.2, short_positive p.1 p.2⟩

theorem positiveRoot_coordinates (a : OrbitIndex) :
    (positiveRoot a).val.val = coordinates a := by
  cases a <;> rfl

theorem positiveRoot_injective : Function.Injective positiveRoot := by
  intro a b hab
  apply coordinates_injective
  simpa only [positiveRoot_coordinates] using
    congrArg (fun k : Positive => k.val.val) hab

theorem positiveRoot_surjective : Function.Surjective positiveRoot := by
  intro k
  rcases positive_root_cover k.val k.property with ⟨s, j, h⟩ | ⟨s, h⟩
  · refine ⟨Sum.inr (s, j), ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨Sum.inl s, ?_⟩
    apply Subtype.ext
    exact h.symm

def positiveRootEquiv : OrbitIndex ≃ Positive :=
  Equiv.ofBijective positiveRoot ⟨positiveRoot_injective, positiveRoot_surjective⟩

theorem positive_card : Nat.card Positive = 12 := by
  rw [← Nat.card_congr positiveRootEquiv]
  simp [OrbitIndex, Nat.card_eq_fintype_card]

theorem long_height (s : Fin 3) :
    ∑ i, (longRoot s).val i = ![(1 : ℤ), 4, 5] s := by
  fin_cases s <;> decide

theorem short_height (s k : Fin 3) :
    ∑ i, (shortRoot s k).val i = ![(1 : ℤ), 2, 3] s := by
  fin_cases s <;> fin_cases k <;> decide

end SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
