import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions
import SymmetricSubgroupAsymptotics.BinaryCarrierMixedRankGap
import SymmetricSubgroupAsymptotics.PermutationFullBlockRankGap
import SymmetricSubgroupAsymptotics.BinaryMenuCayley4T1
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder

/-!
# The strict rank gap on the original finite noncritical alphabet

The thirteen colours are the literal regular C4 action and all twelve
original carrier actions. Fixed epimorphisms supply the carrier rank bounds;
the C4 bound uses its one original permutation generator. A full occurrence
of any of these actions forces a gap for the complete original binary
subgroup, including every correlation with its remaining original points.
This supplies a small-support rank input, not an asymptotic counting bound.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryNoncriticalActionRankGap

inductive Kind
  | cyclicFour
  | carrier (target : BinaryCarrierOriginalActions.Target)
  deriving DecidableEq, Fintype

def points : Kind → Type
  | .cyclicFour => Fin 4
  | .carrier t => BinaryCarrierOriginalActions.points t

instance (k : Kind) : Fintype (points k) := by
  cases k <;> dsimp [points] <;> infer_instance

/-- Every action uses its original ordered permutation generators. -/
def action : (k : Kind) → Subgroup (Equiv.Perm (points k))
  | .cyclicFour => Subgroup.closure (Set.range BinaryMenuCayley4T1.generators)
  | .carrier t => BinaryCarrierOriginalActions.action t

theorem original_cyclicFour_rank_le_one :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (action .cyclicFour)) ≤ 1 := by
  change Module.finrank (ZMod 2) (PrimeCharacters 2
    (Subgroup.closure (Set.range BinaryMenuCayley4T1.generators))) ≤ 1
  simpa only [Fintype.card_fin] using
    primeCharacterRank_le_generating_tuple 2
      (closureGenerators BinaryMenuCayley4T1.generators)
      (closureGenerators_full BinaryMenuCayley4T1.generators)

/-- The degree belongs to the actual original target action, not to an
arbitrary representation of the master quotient. -/
theorem original_carrier_rank_gap (t : BinaryCarrierOriginalActions.Target) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (BinaryCarrierOriginalActions.action t)) + 1 ≤
      Nat.card (BinaryCarrierOriginalActions.points t) / 2 := by
  have h := BinaryCarrierMixedRankGap.quotient_rank_gap
    (BinaryCarrierOriginalActions.sourceKind t)
    (BinaryCarrierOriginalActions.hom t) (BinaryCarrierOriginalActions.hom_surjective t)
  have hc : Fintype.card (BinaryCarrierMixedActions.points
      (BinaryCarrierOriginalActions.sourceKind t)) =
        Fintype.card (BinaryCarrierOriginalActions.points t) := by
    cases t with
    | degree8 t => cases t <;> rfl
    | degree16 m => rfl
  rw [hc] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem action_rank_gap (k : Kind) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (action k)) + 1 ≤ Nat.card (points k) / 2 := by
  cases k with
  | cyclicFour =>
      have h := original_cyclicFour_rank_le_one
      change Module.finrank (ZMod 2) (PrimeCharacters 2 (action .cyclicFour)) + 1 ≤
        Nat.card (Fin 4) / 2
      simp only [Nat.card_fin]
      omega
  | carrier t => exact original_carrier_rank_gap t

/-- One retained actual full noncritical block suffices. Other original
points and all couplings are unrestricted; no rank premise is supplied. -/
theorem full_block_rank_gap {X : Type} [Finite X]
    (J : Subgroup (Equiv.Perm X)) (hJ : IsPGroup 2 J) (k : Kind)
    (B : FullPermutationBlock J (action k)) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) + 1 ≤ Nat.card X / 2 :=
  B.rank_add_one_le_half hJ (action_rank_gap k)

/-- A literal full physical profile, with its original noncritical colour
and occurrence retained. The subgroup need not split as a product. -/
theorem original_profile_rank_gap {ι X : Type} [Fintype ι] [Finite X]
    (k : ι → Kind) (m : ι → ℕ)
    (e : OrbitProfilePoints (fun i => points (k i)) m ≃ X)
    (J : Subgroup (Equiv.Perm X)) (hJ : IsPGroup 2 J)
    (hfull : OrbitProfileFullOn (fun i => action (k i)) e J)
    (i : ι) (j : Fin (m i)) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) + 1 ≤ Nat.card X / 2 :=
  full_block_rank_gap J hJ (k i) (hfull.fullBlock i j)

theorem original_profile_rank_le_half_sub_one {ι X : Type} [Fintype ι] [Finite X]
    (k : ι → Kind) (m : ι → ℕ)
    (e : OrbitProfilePoints (fun i => points (k i)) m ≃ X)
    (J : Subgroup (Equiv.Perm X)) (hJ : IsPGroup 2 J)
    (hfull : OrbitProfileFullOn (fun i => action (k i)) e J)
    (i : ι) (j : Fin (m i)) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) ≤ Nat.card X / 2 - 1 := by
  have h := original_profile_rank_gap k m e J hJ hfull i j
  omega

end SymmetricSubgroupAsymptotics.BinaryNoncriticalActionRankGap
