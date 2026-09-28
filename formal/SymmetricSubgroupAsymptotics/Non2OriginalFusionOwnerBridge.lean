import SymmetricSubgroupAsymptotics.Non2OriginalFusionPayloadSelection
import SymmetricSubgroupAsymptotics.Non2OwnerCapacityFrontier

/-!
# Earlier ownership gives an empty residual axis fibre

The option-valued nonbinary selection assigns coefficient zero to an absent
normal axis only after its residual surviving-epimorphism fibre has been shown
empty on every complete source.  This file derives that exact statement from
physical earlier ownership of every Goursat reconstruction on the axis.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- If the physical predicate rejects every literal reconstruction on one
normal axis and complete source, its surviving epimorphism count is zero. -/
theorem fusionSurvivingEpiCount_eq_zero_of_rejected
    {w b : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hreject : ∀ β : GroupEpimorphism J (U ⧸ N.1),
      ¬ P (fusionFullGoursatEncode N J β).1) :
    fusionSurvivingEpiCount U P N J = 0 := by
  unfold fusionSurvivingEpiCount
  letI : IsEmpty { β : GroupEpimorphism J (U ⧸ N.1) //
      P (fusionFullGoursatEncode N J β).1 } :=
    ⟨fun β ↦ hreject β.1 β.2⟩
  simp

/-- Exact owner-to-zero bridge for the appended residual owner.  If every
Goursat reconstruction on an axis is accepted by some earlier owner, none can
satisfy first ownership by the final residual branch. -/
theorem fusionSurvivingEpiCount_residual_eq_zero_of_earlierOwned
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (howned : ∀ β : GroupEpimorphism J (U ⧸ N.1),
      ∃ i : Fin r,
        Earlier (w + b) i
          (relabelSubgroup finSumFinEquiv
            ((fusionFullGoursatEncode N J β).1.map
              (fusionOrbitAction U)))) :
    fusionSurvivingEpiCount U
        (ordinaryFirstOwnerLocalPredicate U
          (ownerOrResidualEligible Earlier (w + b)) (Fin.last r))
        N J = 0 := by
  apply fusionSurvivingEpiCount_eq_zero_of_rejected U _ N J
  intro β hresidual
  obtain ⟨i, hi⟩ := howned β
  have hnone : ∀ j : Fin r,
      ¬ Earlier (w + b) j
        (relabelSubgroup finSumFinEquiv
          ((fusionFullGoursatEncode N J β).1.map
            (fusionOrbitAction U))) :=
    (firstOwned_ownerOrResidual_last_iff Earlier _).mp hresidual.2
  exact hnone i hi

/-- The actual axis dichotomy.  Its capacity branch contains the complete
usable nonbinary payload.  Its earlier branch proves ownership for every
complete source and every literal Goursat reconstruction on the axis. -/
inductive Non2OriginalFusionAxisOutcome (s : ℕ)
    (U : Subgroup (Equiv.Perm (Fin (2 * s))))
    (N : {N : Subgroup U // N.Normal})
    (EarlierOwned : ∀ b, Subgroup (U × Equiv.Perm (Fin b)) → Prop) where
  | capacity (data : Non2OriginalFusionAxisPayload s U N)
  | earlier (owned : ∀ b (J : Subgroup (Equiv.Perm (Fin b)))
      (β : GroupEpimorphism J (U ⧸ N.1)),
      EarlierOwned b (fusionFullGoursatEncode N J β).1)

namespace Non2OriginalFusionAxisOutcome

variable {s : ℕ} {U : Subgroup (Equiv.Perm (Fin (2 * s)))}
variable {N : {N : Subgroup U // N.Normal}}
variable {EarlierOwned : ∀ b, Subgroup (U × Equiv.Perm (Fin b)) → Prop}

/-- Forget the earlier-owner witness only after it has been retained in the
outcome. -/
def payload? (O : Non2OriginalFusionAxisOutcome s U N EarlierOwned) :
    Option (Non2OriginalFusionAxisPayload s U N) :=
  match O with
  | .capacity A => some A
  | .earlier _ => none

/-- Absence from `payload?` derives the exact zero-fibre premise whenever
the residual predicate excludes physical earlier ownership. -/
theorem survivingEpiCount_eq_zero_of_payload?_eq_none
    (O : Non2OriginalFusionAxisOutcome s U N EarlierOwned)
    {b : ℕ} (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hdisjoint : ∀ H, P H → ¬ EarlierOwned b H)
    (hO : O.payload? = none)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J = 0 := by
  cases O with
  | capacity A => simp [payload?] at hO
  | earlier howned =>
      apply fusionSurvivingEpiCount_eq_zero_of_rejected U P N J
      intro β hP
      exact hdisjoint _ hP (howned b J β)

end Non2OriginalFusionAxisOutcome

section OutcomeMenu

variable {ι : Type*} [Fintype ι]
variable (s : ι → ℕ)
variable (U : ∀ i, Subgroup (Equiv.Perm (Fin (2 * s i))))
variable (EarlierOwned : ∀ i b,
  Subgroup (U i × Equiv.Perm (Fin b)) → Prop)
variable (O : ∀ i (N : {N : Subgroup (U i) // N.Normal}),
  Non2OriginalFusionAxisOutcome (s i) (U i) N (EarlierOwned i))

def non2OutcomePayload? (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) :
    Option (Non2OriginalFusionAxisPayload (s i) (U i) N) :=
  (O i N).payload?

/-- The complete owner-or-capacity recurrence.  Zero on an excluded axis is
a conclusion of its retained ownership witness and the residual disjointness
condition, rather than a supplied numerical premise. -/
theorem non2OriginalFusion_outcome_direct_recurrence
    (hs : ∀ i, 24 ≤ s i)
    (n : ℕ) (hn : ∀ i, 2 * s i ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i,
      Subgroup (U i × Equiv.Perm (Fin (n - 2 * s i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H ∈ F, ∃ i,
      H ∈ FusionCanonicalFamily (U i) (hn i) (P i))
    (hdisjoint : ∀ i H, P i H →
      ¬ EarlierOwned i (n - 2 * s i) H) :
    (Nat.card F : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n,
        non2OriginalFusionPayloadDirectRow s U
            (non2OutcomePayload? s U EarlierOwned O) n m *
          ((subgroupCount m : ℝ) / exactBenchmark m) := by
  apply non2OriginalFusion_payload_direct_recurrence s U
    (non2OutcomePayload? s U EarlierOwned O) hs n hn F P hP hcover
  intro i N hnone J
  exact (O i N).survivingEpiCount_eq_zero_of_payload?_eq_none
    (P i) (hdisjoint i) hnone J

end OutcomeMenu

end SymmetricSubgroupAsymptotics

end
