import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedCenter
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! An actual proper subgroup of the pinned original Ree group has
index at most q^3+1. It is the pullback of the actual fixed Borel to the
actual derived group. The whole fixed-group coset action is faithful by
the proved trivial normal core; no transitivity or model recognition is
assumed for the original projective quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexPointUpper
open PrimitiveSocleRawStructure CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoPositiveDerived CFSGReeGTwoFixedRankOneGeometry
open CFSGReeGTwoFixedCardinalitySylow CFSGReeGTwoBorelCore CFSGReeGTwoDerivedCenter
attribute [local instance] fixedModel_finite

theorem fixed_borel_index (m : ℕ) :
    (borelGroup m).index=(3^(2*m+1))^3+1 := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=borelGroup m))
  calc
    Nat.card (borelGroup m)*(borelGroup m).index=Nat.card (originalModelFixed m) :=
      (borelGroup m).card_mul_index
    _=Nat.card (borelGroup m)*((3^(2*m+1))^3+1) := by
      rw [fixed_group_card,borelGroup_card]

def derivedPointStabilizer (m : ℕ) : Subgroup (commutator (originalModelFixed m)) :=
  (borelGroup m).comap (commutator (originalModelFixed m)).subtype

theorem derivedPointStabilizer_proper (m : ℕ) (hm : 1≤m) :
    derivedPointStabilizer m≠⊤ := by
  intro he
  have hDB : commutator (originalModelFixed m)≤borelGroup m := by
    intro g hg
    have h : (⟨g,hg⟩:commutator (originalModelFixed m))∈derivedPointStabilizer m := by
      rw [he]
      exact Subgroup.mem_top _
    exact h
  have hD := normal_le_borel_eq_bot m (commutator (originalModelFixed m)) hDB
  obtain ⟨u,hu,hn⟩ := fixed_positive_nonidentity m
  have hd := fixedPositiveGroup_le_commutator m hm hu
  rw [hD] at hd
  exact hn hd

theorem derivedPointStabilizer_index_le (m : ℕ) :
    (derivedPointStabilizer m).index≤(3^(2*m+1))^3+1 := by
  change ((borelGroup m).comap (commutator (originalModelFixed m)).subtype).index≤_
  rw [Subgroup.index_comap]
  have hn : (borelGroup m).relIndex ⊤≠0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  calc
    (borelGroup m).relIndex (commutator (originalModelFixed m)).subtype.range≤
        (borelGroup m).relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top hn
    _=(borelGroup m).index := by rw [Subgroup.relIndex_top_right]
    _=(3^(2*m+1))^3+1 := fixed_borel_index m

theorem derived_leastProperIndex_le (m : ℕ) (hm : 1≤m) (ell : ℕ)
    (hell : LeastProperIndex (commutator (originalModelFixed m)) ell) :
    ell≤(3^(2*m+1))^3+1 :=
  (hell.2 _ (derivedPointStabilizer_proper m hm)).trans (derivedPointStabilizer_index_le m)

theorem original_leastProperIndex_le (m : ℕ) (hm : 1≤m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeG2 m) ell) : ell≤(3^(2*m+1))^3+1 :=
  derived_leastProperIndex_le m hm ell
    (CFSGReduction.leastProperIndex_of_mulEquiv (originalReeEquivDerived m hm) ell hell)

def originalPointAction (m : ℕ) (hm : 1≤m) : CFSG.Models.ReeG2 m→*
    Equiv.Perm (originalModelFixed m⧸borelGroup m) :=
  (fixedCosetAction m).comp
    ((commutator (originalModelFixed m)).subtype.comp (originalReeEquivDerived m hm).toMonoidHom)

theorem originalPointAction_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (originalPointAction m hm) :=
  (fixedCosetAction_injective m).comp
    ((commutator (originalModelFixed m)).subtype_injective.comp (originalReeEquivDerived m hm).injective)

theorem originalPointSpace_card (m : ℕ) :
    Nat.card (originalModelFixed m⧸borelGroup m)=(3^(2*m+1))^3+1 :=
  (borelGroup m).index_eq_card.symm.trans (fixed_borel_index m)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexPointUpper
