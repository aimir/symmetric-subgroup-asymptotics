import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierOwnerCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairConcreteInterface

/-!
# Restricting the earlier-owner envelopes to the no-C3 source

The 53 historical earlier owners were inserted before the complete regular-
`C3` family was partitioned out.  Their local counting theorems therefore
have the broader pre-`E7`, non-pair complete-source predicate as domain.

This file proves the common restriction step once.  The no-pair/no-`C3`
predicate is a literal subtype of the broader predicate, so every checked
direct owner envelope remains valid with the same comparator group, faithful
action, and numerical parameters.  No owner label is turned into a predicate
here: the predicates supplied by the broad concrete catalogue are retained
verbatim.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Restricting a complete-source predicate can only decrease the literal
surviving-epimorphism count on an unchanged action and normal axis. -/
theorem fusionSurvivingEpiCount_mono
    {w b : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {P Q : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    (hPQ : ∀ H, P H → Q H)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionSurvivingEpiCount U Q N J := by
  unfold fusionSurvivingEpiCount
  let f : {beta : GroupEpimorphism J (U ⧸ N.1) //
      P (fusionFullGoursatEncode N J beta).1} →
      {beta : GroupEpimorphism J (U ⧸ N.1) //
        Q (fusionFullGoursatEncode N J beta).1} :=
    fun beta => ⟨beta.1, hPQ _ beta.2⟩
  have hf : Function.Injective f := by
    intro beta gamma h
    apply Subtype.ext
    simpa only [f] using congrArg
      (fun x : {delta : GroupEpimorphism J (U ⧸ N.1) //
        Q (fusionFullGoursatEncode N J delta).1} => x.1) h
  exact_mod_cast Nat.card_le_card_of_injective f hf

namespace Non2UnipotentPrefixFiniteMenu

/-- Forgetting the no-regular-`C3` conjunct recovers the broader non-pair
first-owner predicate. -/
theorem preE7NoPairNoC3FirstOwnerPredicate_implies_nonPair
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : PreE7NonPairFirstOwnerIndex r w)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w i × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3FirstOwnerPredicate Earlier w i b H →
      preE7NonPairFirstOwnerPredicate Earlier w i b H :=
  fun h => h.1

/-- Every direct envelope for the broad non-pair source restricts to the
no-pair/no-`C3` source with coefficient one and the same complete quotient
weight. -/
theorem preE7NoPairNoC3_ownedEnvelope_of_nonPair
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : PreE7NonPairFirstOwnerIndex r w)
    (N : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
    {R : Type*} [Group R] [Finite R]
    (h : ∀ J : Subgroup (Equiv.Perm (Fin b)),
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
          (preE7NonPairFirstOwnerPredicate Earlier w i b) N J ≤
        completeQuotientWeight (R := R) J)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
        (preE7NoPairNoC3FirstOwnerPredicate Earlier w i b) N J ≤
      completeQuotientWeight (R := R) J :=
  (fusionSurvivingEpiCount_mono
    (preE7NoPairNoC3FirstOwnerPredicate_implies_nonPair Earlier i)
    N J).trans (h J)

/-- Structural restriction of an already checked broad non-pair owner datum.
The actual earlier-owner predicates are unchanged; only their complete-source
domain is narrowed by the no-regular-`C3` conjunct. -/
noncomputable def PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3EarlierComparatorCore r where
  Earlier := D.Earlier
  earlier_natural := D.earlier_natural
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  Owned := D.Owned
  v := D.v
  action := D.action
  action_injective := D.action_injective
  owned_envelope := by
    intro w i b N hN J
    exact preE7NoPairNoC3_ownedEnvelope_of_nonPair
      (ownerOrResidualEligible D.Earlier) i N
      (D.owned_envelope w i b N hN) J

/-- Numerical decoration transported unchanged from the broad non-pair datum
to its narrowed structural core. -/
noncomputable def PreE7NoPairNoC3OwnerNumerics.ofNonPairOwnerData
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3OwnerNumerics
      (PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData D) where
  C := D.C
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  coefficient_nonneg := D.coefficient_nonneg
  alpha_eq := D.alpha_eq

/-- Complete restriction of a broad non-pair owner datum.  This is the
canonical route by which the actual 53-family catalogue, once constructed on
its original source, enters the final no-pair/no-`C3` frontier. -/
noncomputable def PreE7NonPairOwnerComparatorData.restrictNoC3
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3OwnerData r :=
  (PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData D).withNumerics
    (PreE7NoPairNoC3OwnerNumerics.ofNonPairOwnerData D)

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_Earlier
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.Earlier = D.Earlier := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_Owned
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.Owned = D.Owned := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_C
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.C = D.C := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_parameters
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.v = D.v ∧
      D.restrictNoC3.eta = D.eta ∧
      D.restrictNoC3.delta = D.delta ∧
      D.restrictNoC3.cutoff = D.cutoff ∧
      D.restrictNoC3.alpha = D.alpha := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
