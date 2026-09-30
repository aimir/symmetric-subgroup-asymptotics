import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation
import SymmetricSubgroupAsymptotics.C1OwnerAggregate
import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockEpiBound

/-!
# Degree-six rows on aligned high-C3 cells

An aligned degree-six cell retains the literal high normal pair on its
selected transitive action.  Rerunning the degree-six dichotomy on that
action gives either the odd-index-two owner or the two-by-three binary block
frame.  In both cases every original normal quotient has at most a fixed
constant times `2^(8b/15)` onto maps from a degree-`b` source, so the
complete original normal menu feeds the degree-six numerical row.  The
cyclic binary-module owner is the second alternative, recovered here from
its literal frame.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniform quotient constants transport along a group isomorphism. -/
theorem quotientConstants_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : ℝ)
    (h : ∀ (M : Subgroup H) [M.Normal], ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (H ⧸ M)) : ℝ) ≤ C * (2 : ℝ) ^ (x * b)) :
    ∀ (N : Subgroup G) [N.Normal], ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (G ⧸ N)) : ℝ) ≤ C * (2 : ℝ) ^ (x * b) := by
  intro N hN
  haveI hM : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hN e.toMonoidHom e.surjective
  obtain ⟨C, hC, hbound⟩ := h (N.map e.toMonoidHom)
  refine ⟨C, hC, fun b J => ?_⟩
  rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
    (QuotientGroup.congr N (N.map e.toMonoidHom) e rfl)]
  exact hbound b J

/-- Uniform constants for every original normal quotient feed the complete
numerical row of an earlier owner. -/
theorem c1EarlierPhysical_owner_bound_of_quotientConstants (r : C1EarlierRow)
    (U : Subgroup (Equiv.Perm (Fin (c1EarlierWidth r))))
    (h : ∀ (N : Subgroup U) [N.Normal], ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
          C * (2 : ℝ) ^ (c1EarlierExponent r * b)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + c1EarlierWidth r) ≤
        c1EarlierKernel b r D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  choose C hC0 hC using fun N : {N : Subgroup U // N.Normal} => @h N.1 N.2
  have hsumnn : 0 ≤ ∑ N, C N := Finset.sum_nonneg (fun N _ => hC0 N)
  refine ⟨∑ N, C N, hsumnn, fun b P hP => ?_⟩
  apply c1EarlierPhysical_owner_bound r U b P hP
  intro J
  have haxis (N : {N : Subgroup U // N.Normal}) :
      fusionSurvivingEpiCount U P N J ≤ C N * (2 : ℝ) ^ (c1EarlierExponent r * b) := by
    have hsub : Nat.card { β : GroupEpimorphism J (U ⧸ N.1) //
        P (fusionFullGoursatEncode N J β).1 } ≤
        Nat.card (GroupEpimorphism J (U ⧸ N.1)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hsubR : fusionSurvivingEpiCount U P N J ≤
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionSurvivingEpiCount
      exact_mod_cast hsub
    exact hsubR.trans (hC N b J)
  have hE : (0 : ℝ) ≤ (2 : ℝ) ^ (c1EarlierExponent r * b) := by positivity
  have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  calc (∑ N : {N : Subgroup U // N.Normal}, fusionSurvivingEpiCount U P N J)
      ≤ ∑ N : {N : Subgroup U // N.Normal},
          C N * (2 : ℝ) ^ (c1EarlierExponent r * b) :=
        Finset.sum_le_sum (fun N _ => haxis N)
    _ = (∑ N, C N) * (2 : ℝ) ^ (c1EarlierExponent r * b) := by rw [Finset.sum_mul]
    _ ≤ (∑ N, C N) * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE hb) hsumnn

/-- Every original normal quotient of an aligned degree-six action has a
uniform `2^(8b/15)` epimorphism constant. -/
theorem degreeSix_alignedAction_quotientConstants
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive U (Fin 6)]
    (hU : C3HighAlignedAction U) :
    ∀ (N : Subgroup U) [N.Normal], ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
        (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
          C * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  obtain ⟨N0, hN0, hHigh, _⟩ := hU
  letI := hN0
  have hHigh' : 3 * Nat.card (Fin 6) <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N0) := by
    simpa using hHigh
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock hPrimitive (A := U) (Ω := Fin 6)
      N0 (by simp) hHigh' with hOdd | ⟨ω₀, D, hFibre, hPoints⟩
  · obtain ⟨W⟩ := hOdd
    intro N hN
    refine ⟨(Nat.card (U ≃* U) : ℝ) + Nat.card ((U ⧸ N) ≃* (U ⧸ N)) + 1,
      by positivity, fun b J => ?_⟩
    exact W.quotientEpimorphism_bound hKP (by simp) N b J
  · let points : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hPoints
    let F := D.binaryBlockFrame hFibre points
    have hTop : Nat.card F.top.range = 3 :=
      D.binaryBlockFrame_top_card N0 hFibre hPoints hHigh' points
    obtain ⟨B⟩ := F.blockCoordinates_nonempty hTop
    apply quotientConstants_of_mulEquiv D.originalPermutationEquiv
    intro M hM
    refine ⟨(Nat.card ((D.originalPermutationImage ⧸ M) ≃*
        (D.originalPermutationImage ⧸ M)) : ℝ) + 1, by positivity, fun b J => ?_⟩
    exact B.quotientEpimorphism_bound M hKP b J

/-- The complete physical degree-six row on an aligned selected action. -/
theorem degreeSix_alignedAction_physical_owner_bound
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive U (Fin 6)]
    (hU : C3HighAlignedAction U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 6) ≤
        c1EarlierKernel b .degreeSix D
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 6)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) :=
  c1EarlierPhysical_owner_bound_of_quotientConstants .degreeSix U
    (degreeSix_alignedAction_quotientConstants hPrimitive hKP U hU)

/-- An aligned degree-six cell, whether its intrinsic owner is the
odd-index-two owner or the cyclic binary-module owner, satisfies the
degree-six row in the exact form consumed by the aligned continuation. -/
theorem c3HighAligned_degreeSix_local_bound
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.degreeSix) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) .degreeSix D
            (Nat.card (Subgroup.normalizer
              (c3HighAlignedFirstOwnerAction j :
                Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hcard := hj.2
  rw [hkind] at hcard
  change Nat.card (Fin d.width) = 6 at hcard
  simp only [Nat.card_fin] at hcard
  cases d with
  | three => simp [C3HighWidthLabel.width] at hcard
  | four => simp [C3HighWidthLabel.width] at hcard
  | nine => simp [C3HighWidthLabel.width] at hcard
  | twelve => simp [C3HighWidthLabel.width] at hcard
  | twentySeven => simp [C3HighWidthLabel.width] at hcard
  | six =>
      let U : Subgroup (Equiv.Perm (Fin 6)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 6) :=
        Non2TransitiveActionClass.representative_pretransitive i
      obtain ⟨D, hD, hphys⟩ := degreeSix_alignedAction_physical_owner_bound
        hPrimitive hKP U hj.1
      refine ⟨D, hD, fun n hn => ?_⟩
      have hbn : n - 6 + 6 = n := Nat.sub_add_cancel hn
      have hmain := hphys (n - 6)
        (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.six, owner, i⟩ (n - 6))
        (c3HighFirstOwnerPredicate_natural ⟨C3HighWidthLabel.six, owner, i⟩ (n - 6))
      rw [hbn] at hmain
      rw [fusionWidthCanonicalFamily_card]
      exact hmain

end SymmetricSubgroupAsymptotics

end
