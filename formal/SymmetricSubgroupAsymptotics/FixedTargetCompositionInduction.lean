import SymmetricSubgroupAsymptotics.FixedTargetCompositionEnvelope

/-!
# The complete fixed-target composition induction

Every finite target is peeled along the first nontrivial term of an actual
chief series.  The peeled layer is either elementary abelian, where the
Schur lift estimate applies, or nonabelian semisimple, where the exact
outer-fibre theorem applies.  Thus the fixed-target envelope is constructed
for every finite group, with no structural input left as a hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics
namespace FixedTargetCompositionEnvelope

private theorem actualChiefSeries_length_pos
    (G : Type) [Group G] [Finite G] [Nontrivial G]
    (s : ActualChiefSeries G) : 0 < s.length := by
  by_contra h
  have hs0 : s.length = 0 := Nat.eq_zero_of_not_pos h
  have hbt : (⊥ : Subgroup G) = ⊤ := by
    calc
      (⊥ : Subgroup G) = s.subgroup 0 := s.head.symm
      _ = s.subgroup (Fin.last s.length) := by
        congr 1
        ext
        simp [hs0]
      _ = ⊤ := s.last
  exact not_subsingleton G
    (Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbt))

/-- The first nontrivial term of an actual chief series is a literal minimal
normal subgroup of the original group. -/
private theorem firstChief_minimal
    (G : Type) [Group G] [Finite G] [Nontrivial G]
    (s : ActualChiefSeries G)
    (i0 : Fin s.length) (hi0 : i0.1 = 0)
    (E : Subgroup G) (hE : E = s.subgroup i0.succ) :
    E ≠ ⊥ ∧
      ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E := by
  have hcast : i0.castSucc = (0 : Fin (s.length + 1)) := by
    ext
    exact hi0
  have hlow : s.subgroup i0.castSucc = ⊥ := by
    rw [hcast, s.head]
  have hne : E ≠ ⊥ := by
    intro he
    have hstep := s.step i0
    rw [hlow, ← hE, he] at hstep
    exact (lt_irrefl (⊥ : Subgroup G)) hstep
  refine ⟨hne, ?_⟩
  intro K hK hKE
  have h := s.chief i0 K hK (by rw [hlow]; exact bot_le)
    (by simpa [hE] using hKE)
  simpa [hlow, hE] using h

/-- **Fixed-target composition envelope.**  Every finite target has a
polynomial-times-linear-exponent bound obtained from its actual chief
layers. -/
theorem nonempty (G : Type) [Group G] [Finite G] :
    Nonempty (FixedTargetCompositionEnvelope G) := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (G₀ : Type) [Group G₀] [Finite G₀], Nat.card G₀ = n →
        Nonempty (FixedTargetCompositionEnvelope G₀) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ _ _ hcard
      rcases subsingleton_or_nontrivial G₀ with hsub | hntriv
      · letI : Subsingleton G₀ := hsub
        exact ⟨ofSubsingleton G₀⟩
      · letI : Nontrivial G₀ := hntriv
        let s : ActualChiefSeries G₀ := actualChiefSeries G₀
        have hlen : 0 < s.length := actualChiefSeries_length_pos G₀ s
        let i0 : Fin s.length := ⟨0, hlen⟩
        let E : Subgroup G₀ := s.subgroup i0.succ
        letI : E.Normal := s.normal i0.succ
        have hfirst := firstChief_minimal G₀ s i0 rfl E rfl
        have hquot : Nat.card (G₀ ⧸ E) < Nat.card G₀ := by
          rw [← E.index_eq_card, ← E.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [E.index_eq_card]; exact Nat.card_pos)
            (E.one_lt_card_iff_ne_bot.mpr hfirst.1)
        obtain ⟨Q⟩ := ih (Nat.card (G₀ ⧸ E)) (by omega)
          (G₀ ⧸ E) rfl
        by_cases hcomm : IsMulCommutative E
        · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty E hfirst.1 hcomm hfirst.2
          letI : Finite C.V := Finite.of_injective
            (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
            C.equiv.symm.injective
          letI : Finite C.quotientRepresentation :=
            inferInstanceAs (Finite C.V)
          exact ⟨elementaryStep E C Q⟩
        · let C := semisimpleNormalChart_of_nonabelian_minimal E hfirst.2 hcomm
          exact ⟨semisimpleStep E C Q⟩
  exact hmain (Nat.card G) G rfl

/-- A canonical choice of the proved envelope. -/
noncomputable def canonical (G : Type) [Group G] [Finite G] :
    FixedTargetCompositionEnvelope G :=
  Classical.choice (nonempty G)

end FixedTargetCompositionEnvelope
end SymmetricSubgroupAsymptotics

end
