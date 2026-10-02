import SymmetricSubgroupAsymptotics.FixedTargetCompositionEnvelope
import SymmetricSubgroupAsymptotics.ChiefSeriesPrependMinimal

/-!
# Chief-series trace of the fixed-target envelope

The unrestricted fixed-target induction is strengthened with the literal
chief series that pays its exponent.  Its `abelianLength` is exactly the
number of abelian composition edges in that series, so a published
composition-length theorem can be applied without an extra structural input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

structure FixedTargetCompositionTrace
    (G : Type) [Group G] [Finite G] where
  envelope : FixedTargetCompositionEnvelope G
  chief : ActualChiefSeries G
  nonabelianCount : ℕ
  abelianLength_eq : envelope.abelianLength =
    actualChiefSeriesAbelianLength chief
  nonabelianCount_eq : nonabelianCount =
    actualChiefSeriesNonabelianCount chief
  solvable_of_nonabelianCount_eq_zero : nonabelianCount = 0 → IsSolvable G

namespace FixedTargetCompositionTrace

def subsingletonChiefSeries
    (G : Type) [Group G] [Subsingleton G] : ActualChiefSeries G where
  length := 0
  subgroup := fun _ => ⊥
  normal := fun _ => inferInstance
  head := rfl
  last := Subsingleton.elim _ _
  step := fun i => Fin.elim0 i
  chief := fun i => Fin.elim0 i

def ofSubsingleton
    (G : Type) [Group G] [Finite G] [Subsingleton G] :
    FixedTargetCompositionTrace G where
  envelope := FixedTargetCompositionEnvelope.ofSubsingleton G
  chief := subsingletonChiefSeries G
  nonabelianCount := 0
  abelianLength_eq := by
    simp [FixedTargetCompositionEnvelope.ofSubsingleton,
      actualChiefSeriesAbelianLength, subsingletonChiefSeries]
  nonabelianCount_eq := by
    simp [actualChiefSeriesNonabelianCount, subsingletonChiefSeries]
  solvable_of_nonabelianCount_eq_zero := fun _ => inferInstance

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

/-- Every finite target has an envelope whose exponent is traced exactly to
one actual chief series. -/
theorem nonempty (G : Type) [Group G] [Finite G] :
    Nonempty (FixedTargetCompositionTrace G) := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (G₀ : Type) [Group G₀] [Finite G₀], Nat.card G₀ = n →
        Nonempty (FixedTargetCompositionTrace G₀) := by
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
        let c := prependMinimalNormalChiefSeries E hfirst.1 hfirst.2 Q.chief
        have hc := prependMinimalNormalChiefSeries_abelianLength
          E hfirst.1 hfirst.2 Q.chief
        by_cases hcomm : IsMulCommutative E
        · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty
            E hfirst.1 hcomm hfirst.2
          letI : Finite C.V := Finite.of_injective
            (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
            C.equiv.symm.injective
          letI : Finite C.quotientRepresentation := inferInstanceAs (Finite C.V)
          have hcn := prependMinimalNormalChiefSeries_nonabelianCount
            E hfirst.1 hfirst.2 Q.chief
          refine ⟨{
            envelope := FixedTargetCompositionEnvelope.elementaryStep E C Q.envelope
            chief := c
            nonabelianCount := Q.nonabelianCount
            abelianLength_eq := ?_
            nonabelianCount_eq := ?_
            solvable_of_nonabelianCount_eq_zero := ?_ }⟩
          change Module.finrank (ZMod C.p) C.V + Q.envelope.abelianLength =
            actualChiefSeriesAbelianLength c
          rw [hc, ← Q.abelianLength_eq]
          congr 1
          exact (chiefAbelianLength_elementary C.equiv).symm
          · rw [hcn, chiefNonabelianIndicator]
            simp only [if_pos hcomm, zero_add, Q.nonabelianCount_eq]
          · intro hzero
            letI : IsSolvable E := isSolvable_of_comm
              (fun a b => hcomm.is_comm.comm a b)
            letI : IsSolvable (G₀ ⧸ E) :=
              Q.solvable_of_nonabelianCount_eq_zero hzero
            apply solvable_of_ker_le_range E.subtype (QuotientGroup.mk' E)
            simpa only [QuotientGroup.ker_mk', Subgroup.range_subtype] using
              (le_refl E)
        · let C := semisimpleNormalChart_of_nonabelian_minimal
            E hfirst.2 hcomm
          have hcn := prependMinimalNormalChiefSeries_nonabelianCount
            E hfirst.1 hfirst.2 Q.chief
          refine ⟨{
            envelope := FixedTargetCompositionEnvelope.semisimpleStep E C Q.envelope
            chief := c
            nonabelianCount := Q.nonabelianCount + 1
            abelianLength_eq := ?_
            nonabelianCount_eq := ?_
            solvable_of_nonabelianCount_eq_zero := ?_ }⟩
          change Q.envelope.abelianLength = actualChiefSeriesAbelianLength c
          rw [hc, chiefAbelianLength_nonabelian E hcomm, zero_add,
            Q.abelianLength_eq]
          · rw [hcn, chiefNonabelianIndicator, if_neg hcomm, Q.nonabelianCount_eq]
            omega
          · intro hzero
            omega
  exact hmain (Nat.card G) G rfl

noncomputable def canonical (G : Type) [Group G] [Finite G] :
    FixedTargetCompositionTrace G := Classical.choice (nonempty G)

/-- The traced exponent is bounded by an actual composition-series length. -/
theorem abelianLength_le_some_compositionLength
    {G : Type} [Group G] [Finite G]
    (T : FixedTargetCompositionTrace G) :
    ∃ t : SubnormalCompositionSeries G,
      T.envelope.abelianLength ≤ t.chain.length := by
  obtain ⟨t, ht⟩ := actualChiefAbelianLength_le_some_compositionLength T.chief
  exact ⟨t, T.abelianLength_eq.trans_le ht⟩

/-- The exponent charge plus one retained edge for every nonabelian chief
interval is bounded by an actual composition-series length. -/
theorem totalCharge_le_some_compositionLength
    {G : Type} [Group G] [Finite G]
    (T : FixedTargetCompositionTrace G) :
    ∃ t : SubnormalCompositionSeries G,
      T.envelope.abelianLength + T.nonabelianCount ≤ t.chain.length := by
  obtain ⟨t, ht⟩ := actualChiefTotalCharge_le_some_compositionLength T.chief
  exact ⟨t, by simpa [T.abelianLength_eq, T.nonabelianCount_eq] using ht⟩

theorem one_le_nonabelianCount_of_not_solvable
    {G : Type} [Group G] [Finite G]
    (T : FixedTargetCompositionTrace G) (h : ¬ IsSolvable G) :
    1 ≤ T.nonabelianCount := by
  by_contra hz
  apply h
  apply T.solvable_of_nonabelianCount_eq_zero
  omega

end FixedTargetCompositionTrace
end SymmetricSubgroupAsymptotics

end
