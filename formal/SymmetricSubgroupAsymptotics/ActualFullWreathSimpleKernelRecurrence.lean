import SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelFibreCount
import SymmetricSubgroupAsymptotics.ActualFullWreathFamilyFibreSum
import SymmetricSubgroupAsymptotics.FullComponentRegularLocalWeakRank
import SymmetricSubgroupAsymptotics.ActualRankGeneratingTuple

/-! Whole-family nonabelian chief recurrence. All supports, diagonal
correlations and lifts survive the fixed-image count. The quotient tuple
has genuine ordinary rank, bounded by its regular-local action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelRecurrence
open PermutationalWreathProduct ActualFullWreathFamily

def multiplier (k b aut s t : ℕ) (c : ℝ) : ℕ :=
  (2^(t*k)*(2*(1+t*k*aut))^(t*k))*
    b^((t*k)*Nat.ceil (c*WeakTransitiveDegreeInduction.rate (s*t)))

variable {R R' Q I J T : Type} [Group R] [Finite R] [Group R'] [Finite R']
    [Group Q] [Finite Q] [Fintype I] [Nonempty I] [MulAction Q I]
    [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]
    [Group T] [Finite T] [IsSimpleGroup T] [Fintype J]
    (phi : R →* R') (hphi : Function.Surjective phi)
    (eSoc : phi.ker ≃* (J → T)) (hZ : IsCenterless T)

local instance wreathFinite {D : Type} [Group D] [Finite D] :
    Finite (PermutationalWreathProduct D Q I) :=
  Finite.of_injective (fun w : PermutationalWreathProduct D Q I => (w.left,w.right))
    (by
      intro a b h
      apply PermutationalWreathProduct.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

include hphi eSoc hZ in
theorem card_le_quotient_mul
    (c : ℝ)
    (hbudget : ∀ n : ℕ,2≤n → ∀ K : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive K (Fin n) →
        (MarkedC4.genRank K : ℝ)≤c*WeakTransitiveDegreeInduction.rate n)
    (hI : 2≤Nat.card I) :
    Nat.card (Family R Q I)≤Nat.card (Family R' Q I)*
      multiplier (Nat.card J) (Nat.card T) (Nat.card (T ≃* T))
        (Nat.card R') (Nat.card I) c := by
  apply ActualFullWreathFamilyFibreSum.card_le_mul phi hphi
  intro H
  obtain ⟨f,hf⟩ := ActualRankGeneratingTuple.exists_tuple H.val
  have hcount := ActualFullWreathSimpleKernelFibreCount.card_fibre_le
    phi eSoc hZ hphi H f hf
  have hr := FullComponentRegularLocalWeakRank.rank_le_of_uniform c hbudget H.val.subtype
    Subtype.val_injective (ActualFullWreathFamily.top_surjective H) H.property.2 hI
  have hn : MarkedC4.genRank H.val≤
      Nat.ceil (c*WeakTransitiveDegreeInduction.rate (Nat.card R'*Nat.card I)) := by
    exact_mod_cast hr.trans (Nat.le_ceil _)
  exact hcount.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right Nat.card_pos (Nat.mul_le_mul_left _ hn)))

end SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelRecurrence
