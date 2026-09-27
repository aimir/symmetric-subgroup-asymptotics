import SymmetricSubgroupAsymptotics.OddZeroDefectCoverage

/-!
# Complete intrinsic repeated-marker owner bounds

The literal `Fits` owner inside the ordinary remainder splits exhaustively
into positive and zero orbit defect.  The positive branch uses the checked
strictly forward marker row.  The even zero branch enters the intrinsic
binary error unchanged; the odd zero branch uses the exhaustive singleton/
natural-marker coverage theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

abbrev OrdinaryFullFamily (N epsilon : ℕ) :=
  RepeatedMarkerZeroDefect.FullFamily N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OrdinaryPositiveFamily (N epsilon : ℕ) :=
  RepeatedMarkerIntrinsicPositive.Family N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OrdinaryZeroFamily (N epsilon : ℕ) :=
  RepeatedMarkerZeroDefect.Family N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OutsideFitsFamily (N epsilon : ℕ) :=
  {H : OrdinaryRemainderSubgroups (2*N+epsilon) //
    ¬ RepeatedMarkerOrbitProfiles.Fits H.1}

local instance ordinaryFullFamilyFinite (N epsilon : ℕ) :
    Finite (OrdinaryFullFamily N epsilon) :=
  Finite.of_injective
    (fun H : OrdinaryFullFamily N epsilon =>
      (H.1 : Set (Equiv.Perm (Fin (2*N+epsilon)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

def fitsRemainderEquiv (N epsilon : ℕ) :
    {H : OrdinaryRemainderSubgroups (2*N+epsilon) //
      RepeatedMarkerOrbitProfiles.Fits H.1} ≃ OrdinaryFullFamily N epsilon where
  toFun H := ⟨H.1.1,H.2,H.1.2⟩
  invFun H := ⟨⟨H.1,H.2.2⟩,H.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact frontier after completing the repeated-marker owner: the only
remaining ordinary subgroups are those having a literal orbit image outside
the binary/full-S3 alphabet. -/
def ordinaryRemainderPartitionEquiv (N epsilon : ℕ) :
    OrdinaryRemainderSubgroups (2*N+epsilon) ≃
      OrdinaryFullFamily N epsilon ⊕ OutsideFitsFamily N epsilon :=
  (Equiv.sumCompl (fun H : OrdinaryRemainderSubgroups (2*N+epsilon) =>
    RepeatedMarkerOrbitProfiles.Fits H.1)).symm |>.trans
      (Equiv.sumCongr (fitsRemainderEquiv N epsilon) (Equiv.refl _))

theorem ordinaryRemainder_card_partition (N epsilon : ℕ) :
    Nat.card (OrdinaryRemainderSubgroups (2*N+epsilon)) =
      Nat.card (OrdinaryFullFamily N epsilon) +
        Nat.card (OutsideFitsFamily N epsilon) := by
  rw [Nat.card_congr (ordinaryRemainderPartitionEquiv N epsilon),Nat.card_sum]

def outsideFitsRatio (N epsilon : ℕ) : ℝ :=
  (Nat.card (OutsideFitsFamily N epsilon) : ℝ) /
    exactBenchmark (2*N+epsilon)

theorem ordinaryRemainderRatio_partition (N epsilon : ℕ) :
    ordinaryRemainderRatio (2*N+epsilon) =
      (Nat.card (OrdinaryFullFamily N epsilon) : ℝ) /
        exactBenchmark (2*N+epsilon) + outsideFitsRatio N epsilon := by
  unfold ordinaryRemainderRatio outsideFitsRatio
  rw [ordinaryRemainder_card_partition,Nat.cast_add,add_div]

def OutsideOrbit {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) :=
  {o : OrbitProfileFromOrbits.Orbit H //
    ¬ IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∧
      ¬ ∃ e : Fin 3 ≃ o.orbit,
        relabelSubgroup e oddMarkerActionSubgroup =
          OrbitProfileFromOrbits.orbitImage H o}

theorem outsideFits_hasOrbit (N epsilon : ℕ)
    (H : OutsideFitsFamily N epsilon) : Nonempty (OutsideOrbit H.1.1) := by
  have hbad := H.2
  change ¬ ∀ o : OrbitProfileFromOrbits.Orbit H.1.1,
    IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H.1.1 o) ∨
      ∃ e : Fin 3 ≃ o.orbit,
        relabelSubgroup e oddMarkerActionSubgroup =
          OrbitProfileFromOrbits.orbitImage H.1.1 o at hbad
  push Not at hbad
  obtain ⟨o,hp,hs⟩ := hbad
  exact ⟨⟨o,hp,not_exists.mpr hs⟩⟩

abbrev MarkedOutsideFamily (N epsilon : ℕ) :=
  Σ H : OrdinaryRemainderSubgroups (2*N+epsilon), OutsideOrbit H.1

local instance outsideOrbitFinite {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) : Finite (OutsideOrbit H) :=
  Finite.of_injective Subtype.val Subtype.val_injective

local instance markedOutsideFamilyFinite (N epsilon : ℕ) :
    Finite (MarkedOutsideFamily N epsilon) := inferInstance

/-- Choose one literal bad orbit. The whole original physical subgroup is
retained as the first component, so the pointing is injective without a
multiplicity loss. -/
def outsideFitsMarkedEmbedding (N epsilon : ℕ) :
    OutsideFitsFamily N epsilon ↪ MarkedOutsideFamily N epsilon where
  toFun H := ⟨H.1,Classical.choice (outsideFits_hasOrbit N epsilon H)⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg Sigma.fst h

theorem outsideFits_card_le_marked (N epsilon : ℕ) :
    Nat.card (OutsideFitsFamily N epsilon) ≤
      Nat.card (MarkedOutsideFamily N epsilon) :=
  Nat.card_le_card_of_injective (outsideFitsMarkedEmbedding N epsilon)
    (outsideFitsMarkedEmbedding N epsilon).injective

/-- A bad orbit cannot be a singleton or a pair. Degree three remains, and
its cyclic `C3` action is the first required general non-2 application. -/
theorem outsideOrbit_card_gt_two {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (o : OutsideOrbit H) :
    2 < Nat.card o.1.orbit := by
  have hpos : 0 < Nat.card o.1.orbit := by
    letI : Nonempty o.1.orbit := ⟨o.1.out,by
      rw [o.1.orbit_eq_orbit_out Quotient.out_eq']
      exact MulAction.mem_orbit_self o.1.out⟩
    exact Nat.card_pos
  have h1 : Nat.card o.1.orbit ≠ 1 := by
    intro hc
    obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.singleton_chart H o.1 hc
    have hp : IsPGroup 2 (⊤ : Subgroup (Equiv.Perm PUnit.{1})) := by
      intro g
      refine ⟨0,Subtype.ext ?_⟩
      exact Subsingleton.elim _ _
    have hp' := hp.map e.permCongrHom.toMonoidHom
    change IsPGroup 2 (relabelSubgroup e ⊤) at hp'
    exact o.2.1 (he ▸ hp')
  have h2 : Nat.card o.1.orbit ≠ 2 := by
    intro hc
    obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.pair_chart H o.1 hc
    have hp := (BinaryFourPairIntrinsicTarget.criticalAction_isPGroup .c2).map
      e.permCongrHom.toMonoidHom
    change IsPGroup 2 (relabelSubgroup e (criticalActionSubgroup .c2)) at hp
    exact o.2.1 (he ▸ hp)
  omega

theorem even_zero_normalized_le (N : ℕ) :
    (Nat.card (OrdinaryZeroFamily N 0) : ℝ) / exactBenchmark (2*N) ≤
      binaryErrorRatio N := by
  unfold binaryErrorRatio
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast RepeatedMarkerZeroDefect.even_card_le_noncriticalBinary N)
    (exactBenchmark_pos _).le

/-- Exhaustive even repeated-marker owner: a strictly forward positive row
plus the unchanged intrinsic binary error. -/
theorem even_normalized_le (N : ℕ) :
    (Nat.card (OrdinaryFullFamily N 0) : ℝ) / exactBenchmark (2*N) ≤
      (∑ m ∈ Finset.range (2*N),
        MarkerDegreeForwardRow.kernel (2*N) m * ordinarySubgroupRatio m) +
        binaryErrorRatio N := by
  rw [RepeatedMarkerZeroDefect.card_partition,Nat.cast_add,add_div]
  exact add_le_add
    (RepeatedMarkerIntrinsicPositive.positive_card_div_benchmark_le
      N 0 (by omega) (fun H => ¬ IsCriticalSubgroup (2*N) H))
    (even_zero_normalized_le N)

/-- Exhaustive odd repeated-marker owner: the same strictly forward row
plus the checked current/predecessor binary-error transfer. -/
theorem odd_normalized_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card (OrdinaryFullFamily N 1) : ℝ) / exactBenchmark (2*N+1) ≤
      (∑ m ∈ Finset.range (2*N+1),
        MarkerDegreeForwardRow.kernel (2*N+1) m * ordinarySubgroupRatio m) +
        (OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
          OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
            binaryErrorRatio (N-1)) := by
  rw [RepeatedMarkerZeroDefect.card_partition,Nat.cast_add,add_div]
  exact add_le_add
    (RepeatedMarkerIntrinsicPositive.positive_card_div_benchmark_le
      N 1 (by omega) (fun H => ¬ IsCriticalSubgroup (2*N+1) H))
    (OddZeroDefectCoverage.normalized_card_le N hN)

theorem even_remainder_frontier (N : ℕ) :
    ordinaryRemainderRatio (2*N) ≤
      outsideFitsRatio N 0 +
        (∑ m ∈ Finset.range (2*N),
          MarkerDegreeForwardRow.kernel (2*N) m * ordinarySubgroupRatio m) +
        binaryErrorRatio N := by
  have hp := ordinaryRemainderRatio_partition N 0
  simp only [Nat.add_zero] at hp
  rw [hp]
  linarith [even_normalized_le N]

theorem odd_remainder_frontier (N : ℕ) (hN : 1 ≤ N) :
    ordinaryRemainderRatio (2*N+1) ≤
      outsideFitsRatio N 1 +
        (∑ m ∈ Finset.range (2*N+1),
          MarkerDegreeForwardRow.kernel (2*N+1) m * ordinarySubgroupRatio m) +
        (OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
          OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
            binaryErrorRatio (N-1)) := by
  rw [ordinaryRemainderRatio_partition N 1]
  linarith [odd_normalized_le N hN]

end SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

end
