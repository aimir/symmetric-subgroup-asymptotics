import SymmetricSubgroupAsymptotics.ActualWreathCompressionTowerExistence
import SymmetricSubgroupAsymptotics.ActualWreathCompressionLogBudget
import SymmetricSubgroupAsymptotics.ChiefSeriesPrependMinimal
import SymmetricSubgroupAsymptotics.FixedTargetCompositionEnvelope

/-!
# Chief-series trace of the actual wreath compression

The actual wreath tower now retains the half-induced-module capacity at
every elementary step.  This file traces those steps to a literal chief
series of the local component.  Consequently its complete-source exponent
is bounded by the published worst prime slope times one half of the block
count times an actual composition-series length.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- The source-independent coefficient accumulated by the elementary and
semisimple steps of an actual compression tower.  Elementary steps retain
the literal prime-power cost proved by `ActualWreathAffineCapacity`;
semisimple steps retain the fixed automorphism constants of their displayed
simple factors. -/
noncomputable def coefficientConstant :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 1
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (C.p : ℝ) ^ traceyAffineCoefficientExponent
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
          (traceyInducedGeneratorCeiling
            (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
          S.generatorCount S.sourceDegree C.p *
        coefficientConstant next
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      exact FixedTargetCompositionEnvelope.semisimplePolynomialConstant E *
        coefficientConstant next

/-- Total source-polynomial degree contributed by the nonabelian chief
layers of an actual compression tower. -/
def coefficientPolynomialDegree :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℕ
  | _, .terminal _ _ => 0
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact coefficientPolynomialDegree next
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      exact 2 * Fintype.card E.ι + coefficientPolynomialDegree next

theorem coefficientConstant_nonneg :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) → 0 ≤ T.coefficientConstant
  | _, .terminal _ _ => by simp [coefficientConstant]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simp only [coefficientConstant]
      exact mul_nonneg (by positivity) (coefficientConstant_nonneg next)
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      simp only [coefficientConstant]
      exact mul_nonneg
        (FixedTargetCompositionEnvelope.semisimplePolynomialConstant_nonneg E)
        (coefficientConstant_nonneg next)

/-- Exact tower-wide coefficient envelope obtained by multiplying the
retained elementary prime-power bounds and the proved semisimple polynomial
bounds. -/
theorem envelope_coefficient_le :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) → ∀ b,
        T.envelope.coefficient b ≤
          T.coefficientConstant *
            (1 + (b : ℝ)) ^ T.coefficientPolynomialDegree
  | _, .terminal _ _, b => by
      simp [envelope, coefficientConstant, coefficientPolynomialDegree,
        RelativeCompleteSourceEnvelope.identity]
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next, b => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hnext := envelope_coefficient_le next b
      have hnonneg : 0 ≤ next.envelope.coefficient b :=
        next.envelope.coefficient_nonneg b
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le next).envelope.coefficient b =
            H.coefficient * next.envelope.coefficient b := rfl
        _ ≤ ((C.p : ℝ) ^ traceyAffineCoefficientExponent
              (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
              (traceyInducedGeneratorCeiling
                (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
              S.generatorCount S.sourceDegree C.p) *
              next.envelope.coefficient b :=
          mul_le_mul_of_nonneg_right coefficient_le hnonneg
        _ ≤ ((C.p : ℝ) ^ traceyAffineCoefficientExponent
              (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
              (traceyInducedGeneratorCeiling
                (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
              S.generatorCount S.sourceDegree C.p) *
              (next.coefficientConstant *
                (1 + (b : ℝ)) ^ next.coefficientPolynomialDegree) :=
          mul_le_mul_of_nonneg_left hnext (by positivity)
        _ = (ActualWreathCompressionTower.elementary _ _ phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le next).coefficientConstant *
              (1 + (b : ℝ)) ^
                (ActualWreathCompressionTower.elementary _ _ phi hphi C H
                  capacity_le_half capacity_le_log capacity_refined coefficient_le next).coefficientPolynomialDegree := by
          simp only [coefficientConstant, coefficientPolynomialDegree]
          ring
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next, b => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      let J : Subgroup (Equiv.Perm (Fin b)) := ⊤
      have hpoly :=
        FixedTargetCompositionEnvelope.semisimple_outerFactor_le_polynomial E J
      have hcardJ : Nat.card J = Nat.factorial b := by
        dsimp only [J]
        rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
      rw [hcardJ] at hpoly
      have hnext := envelope_coefficient_le next b
      have houter0 : 0 ≤ E.outerFactor
          (Real.logb 2 (Nat.factorial b)) :=
        E.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast Nat.factorial_pos b))
      calc
        (ActualWreathCompressionTower.semisimple _ _ phi hphi C next).envelope.coefficient b =
            E.outerFactor (Real.logb 2 (Nat.factorial b)) *
              next.envelope.coefficient b := by
          rfl
        _ ≤ E.outerFactor (Real.logb 2 (Nat.factorial b)) *
              (next.coefficientConstant *
                (1 + (b : ℝ)) ^ next.coefficientPolynomialDegree) :=
          mul_le_mul_of_nonneg_left hnext houter0
        _ ≤ (FixedTargetCompositionEnvelope.semisimplePolynomialConstant E *
              (1 + (b : ℝ)) ^ (2 * Fintype.card E.ι)) *
              (next.coefficientConstant *
                (1 + (b : ℝ)) ^ next.coefficientPolynomialDegree) :=
          mul_le_mul_of_nonneg_right hpoly
            (mul_nonneg (coefficientConstant_nonneg next) (by positivity))
        _ = (ActualWreathCompressionTower.semisimple _ _ phi hphi C next).coefficientConstant *
              (1 + (b : ℝ)) ^
                (ActualWreathCompressionTower.semisimple _ _ phi hphi C next).coefficientPolynomialDegree := by
          simp only [coefficientConstant, coefficientPolynomialDegree, pow_add]
          ring

/-- Number of abelian composition edges represented by the elementary
local-chief steps of the tower. -/
def abelianLength :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℕ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact Module.finrank (ZMod C.p) C.V + abelianLength next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact abelianLength next

/-- The retained half-capacity at every elementary step bounds the complete
linear source exponent by the worst prime slope times half the block count
times the abelian chief length. -/
theorem envelope_eta_le_abelianLength :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.envelope.eta ≤ fixedTargetCompositionGamma *
          ((Fintype.card I : ℝ) / 2) * T.abelianLength
  | _, .terminal _ _ => by
      simp [envelope, abelianLength, RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hslope := prime_log_slope_le_fixedTargetGamma C.p C.p_prime
      have hgamma : 0 ≤ fixedTargetCompositionGamma := by
        exact (div_nonneg
          (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num))
      have hfirst : Real.logb 2 C.p / C.p * H.capacity ≤
          fixedTargetCompositionGamma *
            ((Module.finrank (ZMod C.p) C.V : ℝ) * Fintype.card I / 2) := by
        calc
          Real.logb 2 C.p / C.p * H.capacity ≤
              fixedTargetCompositionGamma * H.capacity :=
            mul_le_mul_of_nonneg_right hslope H.capacity_nonneg
          _ ≤ fixedTargetCompositionGamma *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * Fintype.card I / 2) :=
            mul_le_mul_of_nonneg_left capacity_le_half hgamma
      have hnext := envelope_eta_le_abelianLength next
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ fixedTargetCompositionGamma *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * Fintype.card I / 2) +
            fixedTargetCompositionGamma * ((Fintype.card I : ℝ) / 2) *
              next.abelianLength := add_le_add hfirst hnext
        _ = fixedTargetCompositionGamma * ((Fintype.card I : ℝ) / 2) *
              (ActualWreathCompressionTower.elementary _ _ phi hphi C H
                capacity_le_half capacity_le_log capacity_refined coefficient_le next).abelianLength := by
            simp only [abelianLength, Nat.cast_add]
            ring
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [envelope, abelianLength,
        RelativeCompleteSourceEnvelope.semisimpleStep] using
        envelope_eta_le_abelianLength next

/-- Exact prime-weighted version of the half-capacity estimate.  An
elementary factor of order `p^a` contributes at most
`(s/4) * a * log₂ p`, since `p ≥ 2`.  Summing retains the actual elementary
logarithmic order budget instead of replacing every prime by the worst
prime slope. -/
theorem envelope_eta_le_elementaryLogBudget_quarter :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.envelope.eta ≤
          ((Fintype.card I : ℝ) / 4) * T.elementaryLogBudget
  | _, .terminal _ _ => by
      simp [envelope, elementaryLogBudget,
        RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hp2 : (2 : ℝ) ≤ C.p := by exact_mod_cast C.p_prime.two_le
      have hlog0 : 0 ≤ Real.logb 2 C.p :=
        Real.logb_nonneg (by norm_num) (by linarith)
      have hinv : (1 : ℝ) / C.p ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num) hp2
      have hslope : Real.logb 2 C.p / C.p ≤ Real.logb 2 C.p / 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) hlog0
      have hfirst : Real.logb 2 C.p / C.p * H.capacity ≤
          ((Fintype.card I : ℝ) / 4) *
            ((Module.finrank (ZMod C.p) C.V : ℝ) * Real.logb 2 C.p) := by
        calc
          Real.logb 2 C.p / C.p * H.capacity ≤
              (Real.logb 2 C.p / 2) * H.capacity :=
            mul_le_mul_of_nonneg_right hslope H.capacity_nonneg
          _ ≤ (Real.logb 2 C.p / 2) *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * Fintype.card I / 2) :=
            mul_le_mul_of_nonneg_left capacity_le_half (by positivity)
          _ = ((Fintype.card I : ℝ) / 4) *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * Real.logb 2 C.p) := by
            ring
      have hnext := envelope_eta_le_elementaryLogBudget_quarter next
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ ((Fintype.card I : ℝ) / 4) *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * Real.logb 2 C.p) +
            ((Fintype.card I : ℝ) / 4) * next.elementaryLogBudget :=
          add_le_add hfirst hnext
        _ = ((Fintype.card I : ℝ) / 4) *
            (ActualWreathCompressionTower.elementary _ _ phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le next).elementaryLogBudget := by
          simp only [elementaryLogBudget]
          ring
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [envelope, elementaryLogBudget,
        RelativeCompleteSourceEnvelope.semisimpleStep] using
        envelope_eta_le_elementaryLogBudget_quarter next

end ActualWreathCompressionTower

/-- An actual compression tower together with the literal local chief
series whose abelian edges are exactly the elementary steps of the tower. -/
structure ActualWreathCompressionTrace
    (S : ActualWreathCompressionState Q I) where
  tower : ActualWreathCompressionTower S
  integralCapacities : tower.IntegralCapacities
  chief : ActualChiefSeries S.D
  abelianLength_eq : tower.abelianLength =
    actualChiefSeriesAbelianLength chief

namespace ActualWreathCompressionTrace

private def subsingletonChiefSeries
    (G : Type) [Group G] [Subsingleton G] : ActualChiefSeries G where
  length := 0
  subgroup := fun _ => ⊥
  normal := fun _ => inferInstance
  head := rfl
  last := Subsingleton.elim _ _
  step := fun i => Fin.elim0 i
  chief := fun i => Fin.elim0 i

private theorem chiefSeries_length_pos
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

/-- Construct the traced tower by the same literal minimal-normal induction
as the untraced existence theorem. -/
theorem nonempty_of_capacity
    (H : ActualWreathElementaryCapacityInput (Q := Q) (I := I))
    (S : ActualWreathCompressionState Q I) :
    Nonempty (ActualWreathCompressionTrace S) := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (S₀ : ActualWreathCompressionState Q I), Nat.card S₀.D = n →
        Nonempty (ActualWreathCompressionTrace S₀) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S₀ hcard
      rcases subsingleton_or_nontrivial S₀.D with hsub | hntriv
      · letI : Subsingleton S₀.D := hsub
        refine ⟨{
          tower := .terminal S₀ hsub
          integralCapacities := trivial
          chief := subsingletonChiefSeries S₀.D
          abelianLength_eq := ?_ }⟩
        simp [ActualWreathCompressionTower.abelianLength,
          actualChiefSeriesAbelianLength, subsingletonChiefSeries]
      · letI : Nontrivial S₀.D := hntriv
        let s : ActualChiefSeries S₀.D := actualChiefSeries S₀.D
        have hlen : 0 < s.length := chiefSeries_length_pos S₀.D s
        let i0 : Fin s.length := ⟨0, hlen⟩
        let E : Subgroup S₀.D := s.subgroup i0.succ
        letI : E.Normal := s.normal i0.succ
        have hfirst := firstChief_minimal S₀.D s i0 rfl E rfl
        let D' := S₀.D ⧸ E
        let phi : S₀.D →* D' := QuotientGroup.mk' E
        have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective E
        have hquot : Nat.card D' < Nat.card S₀.D := by
          rw [← E.index_eq_card, ← E.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [E.index_eq_card]; exact Nat.card_pos)
            (E.one_lt_card_iff_ne_bot.mpr hfirst.1)
        obtain ⟨next⟩ := ih (Nat.card D') (by omega)
          (S₀.quotient D' phi hphi) rfl
        have hker : phi.ker = E := QuotientGroup.ker_mk' E
        have hker_ne : phi.ker ≠ ⊥ := by simpa [hker] using hfirst.1
        have hker_min : ∀ K : Subgroup S₀.D,
            K.Normal → K ≤ phi.ker → K = ⊥ ∨ K = phi.ker := by
          intro K hK hle
          have hleE : K ≤ E := by simpa [hker] using hle
          rcases hfirst.2 K hK hleE with hbot | htop
          · exact Or.inl hbot
          · exact Or.inr (by simpa [hker] using htop)
        let c := prependMinimalNormalChiefSeries E hfirst.1 hfirst.2 next.chief
        have hc := prependMinimalNormalChiefSeries_abelianLength
          E hfirst.1 hfirst.2 next.chief
        by_cases hcomm : IsMulCommutative phi.ker
        · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty
            phi.ker hker_ne hcomm hker_min
          obtain ⟨HC, hhalf, hlog, hrefined, hintegral, hcoeff⟩ :=
            H S₀ D' phi hphi C
          refine ⟨{
            tower := .elementary S₀ D' phi hphi C HC hhalf hlog hrefined hcoeff next.tower
            integralCapacities := ⟨hintegral, next.integralCapacities⟩
            chief := c
            abelianLength_eq := ?_ }⟩
          change Module.finrank (ZMod C.p) C.V + next.tower.abelianLength =
            actualChiefSeriesAbelianLength c
          rw [hc, ← next.abelianLength_eq]
          congr 1
          calc
            Module.finrank (ZMod C.p) C.V = chiefAbelianLength phi.ker :=
              (chiefAbelianLength_elementary C.equiv).symm
            _ = chiefAbelianLength E :=
              chiefAbelianLength_congr (MulEquiv.subgroupCongr hker)
        · let C := semisimpleNormalChart_of_nonabelian_minimal
            phi.ker hker_min hcomm
          refine ⟨{
            tower := .semisimple S₀ D' phi hphi C next.tower
            integralCapacities := next.integralCapacities
            chief := c
            abelianLength_eq := ?_ }⟩
          change next.tower.abelianLength =
            actualChiefSeriesAbelianLength c
          rw [hc, chiefAbelianLength_nonabelian E]
          · simpa only [zero_add] using next.abelianLength_eq
          · intro hEcomm
            apply hcomm
            rw [hker]
            exact hEcomm
  exact hmain (Nat.card S.D) S rfl

/-- Chosen traced tower used by the affine component transfer. -/
noncomputable def canonicalOfCapacity
    (H : ActualWreathElementaryCapacityInput (Q := Q) (I := I))
    (S : ActualWreathCompressionState Q I) :
    ActualWreathCompressionTrace S :=
  Classical.choice (nonempty_of_capacity H S)

/-- The abelian length of the traced tower is bounded by a literal
composition-series length of its local component. -/
theorem abelianLength_le_some_compositionLength
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTrace S) :
    ∃ t : SubnormalCompositionSeries S.D,
      T.tower.abelianLength ≤ t.chain.length := by
  obtain ⟨t, ht⟩ := actualChiefAbelianLength_le_some_compositionLength T.chief
  exact ⟨t, T.abelianLength_eq.trans_le ht⟩

/-- Publication-facing exponent bound through an actual composition series
of the literal local component. -/
theorem envelope_eta_le_some_compositionLength
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTrace S) :
    ∃ t : SubnormalCompositionSeries S.D,
      T.tower.envelope.eta ≤ fixedTargetCompositionGamma *
        ((Fintype.card I : ℝ) / 2) * t.chain.length := by
  obtain ⟨t, ht⟩ := T.abelianLength_le_some_compositionLength
  refine ⟨t, (ActualWreathCompressionTower.envelope_eta_le_abelianLength
    T.tower).trans ?_⟩
  have hfactor : 0 ≤ fixedTargetCompositionGamma *
      ((Fintype.card I : ℝ) / 2) := by
    apply mul_nonneg
    · exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    · positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hfactor

end ActualWreathCompressionTrace
end SymmetricSubgroupAsymptotics

end
