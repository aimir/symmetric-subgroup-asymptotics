import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions

/-! The ACTUAL least-index coset action of the same finite simple group
supplies its ordinary rank from strictly-smaller TRANSITIVE induction.
The same faithful embedding gives factorial order divisibility. Neither
a global Tracey theorem nor a simple two-generator bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleLeastIndexStrictOrdinaryGenerators
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable (T : Type) [Group T] [Finite T] [IsSimpleGroup T]

theorem card_dvd_factorial (ell : ℕ) (hell : LeastProperIndex T ell) :
    Nat.card T ∣ ell.factorial := by
  obtain ⟨H,hH,hi⟩ := hell.1
  letI : Fintype (T ⧸ H) := Fintype.ofFinite _
  have hd := Subgroup.card_dvd_of_injective (MulAction.toPermHom T (T ⧸ H))
    (simple_cosetAction_injective H hH)
  have hperm : Nat.card (Equiv.Perm (T ⧸ H)) = ell.factorial := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,
      ←H.index_eq_card,hi]
  exact hperm ▸ hd

theorem genRank_le_of_strictly_smaller (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex T ell) (hlt : ell < n) :
    MarkedC4.genRank T ≤ traceyPermutationGeneratorCeiling ell := by
  obtain ⟨H,hH,hi⟩ := hell.1
  letI : FaithfulSMul T (T ⧸ H) :=
    ⟨fun {_ _} h => simple_cosetAction_injective H hH (Equiv.ext h)⟩
  have htwo : 2 ≤ Nat.card (T ⧸ H) := by
    rw [←H.index_eq_card]
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hlt' : Nat.card (T ⧸ H) < n := by rw [←H.index_eq_card,hi]; exact hlt
  have hh := rank_of_faithful_transitive_action n hbelow T (T ⧸ H) htwo hlt'
  simpa only [←H.index_eq_card,hi] using hh

theorem exists_generating_finset_of_strictly_smaller (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex T ell) (hlt : ell < n) :
    ∃ s : Finset T, Subgroup.closure (s : Set T) = ⊤ ∧
      s.card ≤ traceyPermutationGeneratorCeiling ell := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := T)
  exact ⟨s,hgen,hs.le.trans (genRank_le_of_strictly_smaller T n ell hbelow hell hlt)⟩

end SymmetricSubgroupAsymptotics.SimpleLeastIndexStrictOrdinaryGenerators
