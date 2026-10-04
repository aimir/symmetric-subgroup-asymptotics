import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

/-!
# Correlated complete-source character intervals

The pointwise character template charges its retained quotient comparator on
every normal axis above the retained subgroup.  For affine exceptional
components that loses the correlation supplied by normal correspondence.
This file keeps that interval intact.  The axes containing `E` inject into
the literal normal-axis menu of `U / E` and are therefore paid once by
`completeQuotientWeight (U / E)`.  Every remaining axis carries a fixed
mixed character certificate; their automorphism coefficients are summed
before the common cold exponential is attached.

The resulting estimate is

`fusionCompleteSourceSum U P J <= Z_J(U / E) + T * 2^(theta*b)`,

where `T` is the finite sum of the literal automorphism counts below `E`.
It is then installed directly as a `PreE7CompleteSourceNumericalData` and a
final rank-tail owner source.  No normal-axis census or precedence claim is
used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

-- Keep both sides of the correlated normal-axis sums on the canonical
-- subtype enumeration.  The project-wide optimized normal-axis `Fintype`
-- enumerates the same finite type, but using it on only one unfolded side
-- obscures the definitional equality needed below.
attribute [-instance] originalNormalFintype

private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

private abbrev NormalAxisAbove {G : Type*} [Group G]
    (E : Subgroup G) :=
  {N : NormalAxis G // E <= N.1}

private abbrev NormalAxisBelow {G : Type*} [Group G]
    (E : Subgroup G) :=
  {N : NormalAxis G // ¬ E <= N.1}

/-- The literal normal axis of `G / E` attached to a normal axis containing
`E`. -/
private def normalAxisAboveMap {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal] :
    NormalAxisAbove E → NormalAxis (G ⧸ E) :=
  fun N =>
    ⟨N.1.1.map (QuotientGroup.mk' E),
      Subgroup.Normal.map N.1.2 (QuotientGroup.mk' E)
        (QuotientGroup.mk'_surjective E)⟩

/-- Normal correspondence is injective on the literal interval above `E`.
This is the only correspondence fact needed for the correlated estimate. -/
private theorem normalAxisAboveMap_injective {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal] :
    Function.Injective (normalAxisAboveMap E) := by
  intro N N' h
  apply Subtype.ext
  apply Subtype.ext
  have hmap : N.1.1.map (QuotientGroup.mk' E) =
      N'.1.1.map (QuotientGroup.mk' E) :=
    congrArg (fun M : NormalAxis (G ⧸ E) => M.1) h
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' E)) hmap
  rw [QuotientGroup.comap_map_mk', QuotientGroup.comap_map_mk',
    sup_eq_right.mpr N.2, sup_eq_right.mpr N'.2] at hcomap
  exact hcomap

/-- The whole literal interval above `E` is one complete quotient weight of
`G / E`.  Distinct original axes stay distinct by normal correspondence. -/
theorem normalAxisAbove_epimorphism_sum_le_completeQuotientWeight
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ N : NormalAxisAbove E,
        (Nat.card (GroupEpimorphism J (G ⧸ N.1.1)) : ℝ)) ≤
      completeQuotientWeight (R := G ⧸ E) J := by
  let κ : NormalAxisAbove E → NormalAxis (G ⧸ E) :=
    normalAxisAboveMap E
  let g : NormalAxis (G ⧸ E) → ℝ := fun M =>
    Nat.card (GroupEpimorphism J ((G ⧸ E) ⧸ M.1))
  have hκ : Function.Injective κ := normalAxisAboveMap_injective E
  have htransport : ∀ N : NormalAxisAbove E,
      (Nat.card (GroupEpimorphism J (G ⧸ N.1.1)) : ℝ) = g (κ N) := by
    intro N
    change (Nat.card (GroupEpimorphism J (G ⧸ N.1.1)) : ℝ) =
      (Nat.card (GroupEpimorphism J
        ((G ⧸ E) ⧸ N.1.1.map (QuotientGroup.mk' E))) : ℝ)
    exact_mod_cast fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (QuotientGroup.quotientQuotientEquivQuotient E N.1.1 N.2).symm
  calc
    (∑ N : NormalAxisAbove E,
        (Nat.card (GroupEpimorphism J (G ⧸ N.1.1)) : ℝ)) =
        ∑ N : NormalAxisAbove E, g (κ N) :=
      Finset.sum_congr rfl (fun N _ => htransport N)
    _ = ∑ M ∈ Finset.univ.image κ, g M := by
      rw [Finset.sum_image (fun N _ N' _ h => hκ h)]
    _ ≤ ∑ M : NormalAxis (G ⧸ E), g M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun M _ _ => Nat.cast_nonneg _)
    _ = completeQuotientWeight (R := G ⧸ E) J := by
      dsimp [g]
      unfold completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]

/-- Structural input for the correlated interval theorem.  The quotient
`U / E` has a faithful comparator action.  Every literal normal axis below
`E` has a mixed character certificate, uniformly bounded by `theta`. -/
structure CompleteCharacterIntervalData {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) : Type 1 where
  E : Subgroup U
  [E_normal : E.Normal]
  quotientDegree : ℕ
  quotientAction : (U ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  theta : ℝ
  quotientCertificate : ∀ N : NormalAxis U, ¬ E ≤ N.1 →
    CharacterQuotientCertificate (U ⧸ N.1)
  quotientCertificate_mixed : ∀ N h,
    (quotientCertificate N h).mode = .mixed
  quotientCertificate_slope : ∀ N h,
    (quotientCertificate N h).slope ≤ theta

attribute [instance] CompleteCharacterIntervalData.E_normal

namespace CompleteCharacterIntervalData

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (D : CompleteCharacterIntervalData U)

/-- The finite coefficient of the character tail, with one automorphism
count for every literal axis below `E`. -/
def tailConstant : ℝ :=
  ∑ N : NormalAxisBelow D.E,
    (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ)

theorem tailConstant_nonneg : 0 ≤ D.tailConstant := by
  unfold tailConstant
  exact Finset.sum_nonneg (fun N _ => Nat.cast_nonneg _)

/-- The surviving fibres on the interval above `E` are paid by one complete
quotient weight of `U / E`. -/
theorem above_source_envelope {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ N : NormalAxisAbove D.E,
        fusionSurvivingEpiCount U P N.1 J) ≤
      completeQuotientWeight (R := U ⧸ D.E) J := by
  calc
    (∑ N : NormalAxisAbove D.E,
        fusionSurvivingEpiCount U P N.1 J) ≤
        ∑ N : NormalAxisAbove D.E,
          (Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) : ℝ) := by
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card U P N.1 J)
    _ ≤ completeQuotientWeight (R := U ⧸ D.E) J :=
      normalAxisAbove_epimorphism_sum_le_completeQuotientWeight D.E J

/-- The complementary literal axes contribute one finite automorphism sum
times the common character slope. -/
theorem below_source_envelope (lit : PreE7CharacterLiterature) {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ N : NormalAxisBelow D.E,
        fusionSurvivingEpiCount U P N.1 J) ≤
      D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
  have haxis : ∀ N : NormalAxisBelow D.E,
      fusionSurvivingEpiCount U P N.1 J ≤
        (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
          (2 : ℝ) ^ (D.theta * b) := by
    intro N
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    calc
      fusionSurvivingEpiCount U P N.1 J ≤
          Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) :=
        fusionSurvivingEpiCount_le_groupEpimorphism_card U P N.1 J
      _ ≤ (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
          (2 : ℝ) ^ ((D.quotientCertificate N.1 N.2).slope * b) :=
        (D.quotientCertificate N.1 N.2).envelope lit b J
      _ ≤ (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
          (2 : ℝ) ^ (D.theta * b) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right
            (D.quotientCertificate_slope N.1 N.2) hb)
  calc
    (∑ N : NormalAxisBelow D.E,
        fusionSurvivingEpiCount U P N.1 J) ≤
        ∑ N : NormalAxisBelow D.E,
          (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
            (2 : ℝ) ^ (D.theta * b) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
      rw [← Finset.sum_mul]
      rfl

/-- The correlated complete-source interval theorem.  The retained quotient
menu and the character tail are each paid once. -/
theorem completeSource_envelope (lit : PreE7CharacterLiterature) {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      completeQuotientWeight (R := U ⧸ D.E) J +
        D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
  let Q : NormalAxis U → Prop := fun N => D.E ≤ N.1
  let f : NormalAxis U → ℝ := fun N =>
    fusionSurvivingEpiCount U P N J
  have hsplit := Fintype.sum_subtype_add_sum_subtype Q f
  calc
    fusionCompleteSourceSum U P J = ∑ N : NormalAxis U, f N := by
      dsimp [f]
      unfold fusionCompleteSourceSum
      change
        Finset.sum (@Finset.univ (NormalAxis U)
            (Subtype.fintype Subgroup.Normal))
            (fun N => fusionSurvivingEpiCount U P N J) =
        Finset.sum (@Finset.univ (NormalAxis U)
            (Subtype.fintype Subgroup.Normal))
            (fun N => fusionSurvivingEpiCount U P N J)
      rfl
    _ = (∑ N : {N : NormalAxis U // Q N}, f N.1) +
        ∑ N : {N : NormalAxis U // ¬ Q N}, f N.1 := hsplit.symm
    _ ≤ completeQuotientWeight (R := U ⧸ D.E) J +
        D.tailConstant * (2 : ℝ) ^ (D.theta * b) :=
      add_le_add (D.above_source_envelope P J)
        (D.below_source_envelope lit P J)

end CompleteCharacterIntervalData

namespace Non2UnipotentPrefixFiniteMenu

/-- Numerical hypotheses needed to install the correlated interval theorem
in the pre-E7 transfer.  The quotient comparator is padded only after the
exact complete-source estimate has been proved. -/
structure PreE7CompleteCharacterIntervalNumerics {w : ℕ}
    {i : PreE7NonPairActionClass w}
    (D : CompleteCharacterIntervalData (preE7NonPairAction w i)) : Prop where
  comparator_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - (max 2 D.quotientDegree : ℕ)) / 8
  theta_window : D.theta ≤ preE7CharacterWindow w
  tail_total_bound : ∀ b, D.tailConstant ≤
    (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7CompleteCharacterIntervalNumerics

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  {D : CompleteCharacterIntervalData (preE7NonPairAction w i)}
  (N : PreE7CompleteCharacterIntervalNumerics D)

def sourceDegree (_N : PreE7CompleteCharacterIntervalNumerics D) : ℕ :=
  max 2 D.quotientDegree

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho N.sourceDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 N.sourceDegree w

def cutoff : ℝ := (N.degree : ℝ) / 8 + N.delta / 2

theorem quotientDegree_le_degree : D.quotientDegree ≤ N.degree :=
  (le_max_right 2 D.quotientDegree).trans (le_max_left _ _)

/-- Complete-source certificate with coefficient one on the retained
quotient menu and the finite character coefficient as its additive tail. -/
noncomputable def certificate (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CompleteSourceComparatorCertificate family w i where
  R := preE7NonPairAction w i ⧸ D.E
  groupR := inferInstance
  finiteR := inferInstance
  v := N.degree
  action := (characterComparatorPadHom N.quotientDegree_le_degree).comp
    D.quotientAction
  action_injective :=
    (characterComparatorPadHom_injective N.quotientDegree_le_degree).comp
      D.quotientAction_injective
  D := fun _ => 1
  T := fun _ => D.tailConstant
  eta := 0
  delta := N.delta
  cutoff := N.cutoff
  alpha := N.cutoff
  theta := D.theta
  alpha_eq := by simp
  D_nonneg := fun _ => zero_le_one
  T_nonneg := fun _ => D.tailConstant_nonneg
  broad_source_envelope := by
    intro b J
    simpa using D.completeSource_envelope lit
      (preE7NoPairNoC3BroadActionPredicate w i b) J

/-- The standard padding numerics, with the supplied character window as the
only nonzero tail condition. -/
theorem parameters (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (N.certificate lit family).v (N.certificate lit family).eta
      (N.certificate lit family).delta (N.certificate lit family).cutoff
      (N.certificate lit family).alpha (N.certificate lit family).theta := by
  simpa [certificate, sourceDegree, degree, delta, cutoff] using
    (preE7Padded_entryParameters_withTail
      (w := w) (v0 := N.sourceDegree) (eta := (0 : ℝ)) (theta := D.theta)
      (by norm_num) (le_max_left 2 D.quotientDegree)
      (by simpa [sourceDegree] using N.comparator_margin)
      N.theta_window)

/-- Numerical package for the correlated interval theorem. -/
noncomputable def numericalData (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CompleteSourceNumericalData family w i where
  certificate := N.certificate lit family
  parameters := N.parameters lit family
  main_total_bound := by
    intro b
    change (1 : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
    exact Real.one_le_rpow (by norm_num) (by positivity)
  tail_total_bound := by
    intro b
    change D.tailConstant ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
    exact N.tail_total_bound b

/-- Final source exported to the primitive-affine exceptional-cell
consumer. -/
noncomputable def toRankTailSourceOrYonedaTop
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData w i :=
  .inl (N.numericalData lit family).toRankTailOwnerSource

end PreE7CompleteCharacterIntervalNumerics

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
