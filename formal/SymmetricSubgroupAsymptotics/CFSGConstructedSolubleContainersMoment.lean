import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersRate
import SymmetricSubgroupAsymptotics.MarkedC4ConstructedLargeOrbitMoment

/-! The actual constructed soluble cover pays the large-orbit marked
encoding without a labelled-transitive-count hypothesis. Each original
group chooses one containing soluble group, and its actual relative tuple
is recorded there. This removes only the soluble-container use of LMM;
the nonsoluble pre-E7 menu remains a different counting obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Classical BigOperators Topology
namespace SymmetricSubgroupAsymptotics.CFSGConstructedSolubleContainersMoment
open MarkedC4 LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel
open CFSGOrdinaryContainerCoverFormula SolubleContainerOrder

local instance (b : ℕ) : Fintype (CFSGSolubleFullContainerCover.cover b).Index :=
  Fintype.ofFinite _

theorem cover_eventually_exp_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop,
      (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) ≤
        (2 : ℝ) ^ (ε * (b : ℝ) ^ 2) := by
  have hlim : Tendsto (fun b : ℕ =>
      4096 * (Real.logb 2 ((b : ℝ) + 2)) ^ 4 / (b : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2)
      1 (-2) 4 (by norm_num)).comp
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def, mul_div_assoc] using h.const_mul 4096
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with b hb hb1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  have hratio := (div_le_iff₀ hb0).mp hb.le
  have he : 4096 * (b : ℝ) * (Real.logb 2 ((b : ℝ) + 2)) ^ 4 ≤
      ε * (b : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hb0.le]
  exact (CFSGSolubleWreathContainers.cover_card_le_polylog b).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)

theorem words_bound (b l : ℕ) :
    (∑ i : (CFSGSolubleFullContainerCover.cover b).Index,
      (Fintype.card ((CFSGSolubleFullContainerCover.cover b).group i) : ℝ) ^ l) ≤
      (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) *
        (2 : ℝ) ^ (2 * b * l) := by
  let E := CFSGSolubleFullContainerCover.cover b
  have ho (i : E.Index) : (Fintype.card (E.group i) : ℝ) ≤ (2 : ℝ) ^ (2 * b) := by
    letI : IsSolvable (E.group i) := E.soluble i
    have h := SolubleContainerOrder.factor_order
      ElementaryDixonOrderProof.WithoutCatalogue.dixonOrder_of_primitive_inputs
        (Fin b) (E.group i)
    simp only [Fintype.card_fin, Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ _i : E.Index, ((2 : ℝ) ^ (2 * b)) ^ l :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (ho i) l)
    _ = _ := by simp [E, Nat.card_eq_fintype_card, pow_mul]

theorem moment_le_of_relative_tuples {C l b : ℕ} (hC : 2 ≤ C)
    (hrelative : ∀ G : SolublePermutationSubgroup b,
      ∃ t : Fin l → G.val,
        Subgroup.closure (Set.range t ∪ (projection G.val C).ker) = ⊤)
    (r : ℕ) :
    solubleMarkedC4Moment b r ≤
      (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) *
        (2 : ℝ) ^ (2 * b * l) * (2 : ℝ) ^ (2 * r * l) *
          OrbitCutoffFamilies.solubleCount C b r := by
  let E := CFSGSolubleFullContainerCover.cover b
  have hcover (G : SolublePermutationSubgroup b) : ∃ i, G.val ≤ E.group i :=
    E.covers G.val G.property
  choose container hcontainer using hcover
  choose tuple htuple using hrelative
  let K : ∀ G : SolublePermutationSubgroup b, Subgroup G.val :=
    fun G => (projection G.val C).ker
  let P : Subgroup (PermutationGroup b) → Prop :=
    fun J => IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J
  letI : Fintype (ContainerRelativeEncoding.Target P) :=
    inferInstanceAs (Fintype (OrbitCutoffFamilies.SolubleFamily C b))
  have hP (G : SolublePermutationSubgroup b) : P ((K G).map G.val.subtype) := by
    letI : IsSolvable G.val := G.property
    exact (solubleTarget G.val C hC).property
  have hs := ContainerRelativeEncoding.moment_le E.group
    (fun G : SolublePermutationSubgroup b => G.val) Subtype.val_injective
    container hcontainer K tuple htuple P hP r
  have hs' : solubleMarkedC4Moment b r ≤
      (∑ i : E.Index, (Fintype.card (E.group i) : ℝ) ^ l) *
        (2 : ℝ) ^ (2 * r * l) * OrbitCutoffFamilies.solubleCount C b r := by
    simp only [← Nat.card_eq_fintype_card, solubleMarkedC4Moment,
      OrbitCutoffFamilies.solubleCount] at hs ⊢
    convert hs using 1
    congr 1
    apply Finset.sum_congr
    · ext z
      simp
    · intro z _
      rfl
  exact hs'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (words_bound b l) (by positivity))
      (Finset.sum_nonneg (fun _ _ => by positivity)))

theorem exists_cutoff_moment_le (h62 : PublishedProposition62)
    (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b r : ℕ,
      solubleMarkedC4Moment b r ≤
        (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) *
          (2 : ℝ) ^ (2 * b * tupleLength rate b) *
          (2 : ℝ) ^ (2 * r * tupleLength rate b) *
          OrbitCutoffFamilies.solubleCount C b r := by
  obtain ⟨C, hC, ht⟩ := exists_cutoff_relative_tuples h62 rate hrate
  refine ⟨C, hC, ?_⟩
  intro b r
  apply moment_le_of_relative_tuples hC
  intro G
  letI : IsSolvable G.val := G.property
  exact ht b G.val

theorem code_cost_le (ε rate : ℝ) (b r : ℕ)
    (hindex : (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) ≤
      (2 : ℝ) ^ (ε * (b : ℝ) ^ 2)) :
    (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) *
        (2 : ℝ) ^ (2 * b * tupleLength rate b) *
        (2 : ℝ) ^ (2 * r * tupleLength rate b) ≤
      (2 : ℝ) ^ (ε * (b : ℝ) ^ 2 +
        2 * ((b : ℝ) + r) * tupleLength rate b) := by
  calc
    _ ≤ (2 : ℝ) ^ (ε * (b : ℝ) ^ 2) *
        (2 : ℝ) ^ (2 * b * tupleLength rate b) *
        (2 : ℝ) ^ (2 * r * tupleLength rate b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hindex (by positivity)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * b * tupleLength rate b),
        ← Real.rpow_natCast (2 : ℝ) (2 * r * tupleLength rate b),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring

/-- Actual soluble groups need no transitive-count premise for the
large-orbit marked reduction. The ordinary relative-generation input is
retained here and can be derived by its separate CFSG reduction. -/
theorem marked_bound (h62 : PublishedProposition62) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) *
          OrbitCutoffFamilies.solubleCount C b r := by
  let rate : ℝ := δ / 8
  have hrate : 0 < rate := by dsimp [rate]; positivity
  obtain ⟨C, hC, hfinite⟩ := exists_cutoff_moment_le h62 rate hrate
  refine ⟨C, hC, ?_⟩
  filter_upwards [cover_eventually_exp_bound (δ / 4) (by positivity),
    eventually_ge_atTop (⌈8 / δ⌉₊)] with b hmenu hb
  intro r
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hceil : (tupleLength rate b : ℝ) ≤ rate * b + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hrate.le hb0)).le
  have hb' : (8 : ℝ) / δ ≤ b :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hlarge : (8 : ℝ) ≤ δ * b := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hb'
  have hlinear : 2 * ((b : ℝ) + r) ≤ (δ / 4) * ((b : ℝ) + r) ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ δ * ((b : ℝ) + r) - 8 by nlinarith)
      (add_nonneg hb0 hr0)
    nlinarith
  have hquad : (b : ℝ) * ((b : ℝ) + r) ≤ ((b : ℝ) + r) ^ 2 := by
    nlinarith [mul_nonneg hr0 (add_nonneg hb0 hr0)]
  have herr : (δ / 4) * (b : ℝ) ^ 2 +
      2 * ((b : ℝ) + r) * tupleLength rate b ≤ δ * ((b : ℝ) + r) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left hceil
      (show 0 ≤ 2 * ((b : ℝ) + r) by positivity)
    have hs : (b : ℝ) ^ 2 ≤ ((b : ℝ) + r) ^ 2 := by nlinarith
    dsimp [rate] at ht
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ δ / 4 by positivity),
      mul_le_mul_of_nonneg_left hquad (show 0 ≤ δ / 4 by positivity)]
  calc
    solubleMarkedC4Moment b r ≤
        ((Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) *
          (2 : ℝ) ^ (2 * b * tupleLength rate b) *
          (2 : ℝ) ^ (2 * r * tupleLength rate b)) *
          OrbitCutoffFamilies.solubleCount C b r := hfinite b r
    _ ≤ (2 : ℝ) ^ ((δ / 4) * (b : ℝ) ^ 2 +
          2 * ((b : ℝ) + r) * tupleLength rate b) *
          OrbitCutoffFamilies.solubleCount C b r :=
      mul_le_mul_of_nonneg_right (code_cost_le (δ / 4) rate b r hmenu)
        (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) herr)
      (Finset.sum_nonneg (fun _ _ => by positivity))

end SymmetricSubgroupAsymptotics.CFSGConstructedSolubleContainersMoment
