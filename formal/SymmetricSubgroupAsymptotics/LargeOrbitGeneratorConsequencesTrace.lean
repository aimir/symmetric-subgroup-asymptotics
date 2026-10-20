import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesWreath
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import SymmetricSubgroupAsymptotics.ChiefSeriesPrependMinimal
import SymmetricSubgroupAsymptotics.PermutationSectionNormalGenerators

/-! Ordinary generators through every actual elementary local-chief kernel.
The unchanged top retains the other original point orbits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I] [MulAction Q I]

namespace WreathState

/-- Quotient only the selected orbit's local component; retain the whole top. -/
def quotient (S : WreathState Q I)
    (D' : Type) [Group D'] [Finite D']
    (phi : S.D →* D') : WreathState Q I where
  A := S.A ⧸ PermutationalWreathProduct.Compression.kernel S.rho phi
  D := D'
  groupA := inferInstance
  finiteA := inferInstance
  groupD := inferInstance
  finiteD := inferInstance
  rho := PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
  rho_injective :=
    PermutationalWreathProduct.Compression.quotientEmbedding_injective S.rho phi
  top_surjective := by
    intro q
    obtain ⟨a, ha⟩ := S.top_surjective q
    refine ⟨QuotientGroup.mk' (PermutationalWreathProduct.Compression.kernel
      S.rho phi) a, ?_⟩
    change (S.rho a).right = q
    exact ha
  top_pretransitive := S.top_pretransitive

/-- With trivial local component, the selected compression has reached the
whole retained top, including its actions on the other point orbits. -/
theorem genRank_le_top [Finite Q] (S : WreathState Q I)
    [Subsingleton S.D] : genRank S.A ≤ genRank Q := by
  let f := PermutationalWreathProduct.rightHom.comp S.rho
  have hf : Function.Injective f := by
    intro a b hab
    apply S.rho_injective
    apply PermutationalWreathProduct.ext
    · funext i
      exact Subsingleton.elim _ _
    · exact hab
  let e := MulEquiv.ofBijective f ⟨hf, S.top_surjective⟩
  exact genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective

end WreathState

/-- One ceiling per unit of local dimension bounds the ceiling in any local
dimension; thus no rounding cost is charged per chosen chief factor. -/
theorem traceyInducedGeneratorCeiling_le_mul (a s : ℕ) :
    traceyInducedGeneratorCeiling a s ≤
      a * traceyInducedGeneratorCeiling 1 s := by
  unfold traceyInducedGeneratorCeiling
  apply Nat.ceil_le.mpr
  push_cast
  have h := Nat.le_ceil (4 * (1 : ℝ) * s / Real.sqrt (Real.logb 2 s))
  calc
    4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) =
        a * (4 * 1 * s / Real.sqrt (Real.logb 2 s)) := by ring
    _ ≤ a * ⌈4 * (1 : ℝ) * s / Real.sqrt (Real.logb 2 s)⌉₊ :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg a)

private def trivialChiefSeries (G : Type) [Group G] [Subsingleton G] :
    ActualChiefSeries G where
  length := 0
  subgroup := fun _ => ⊥
  normal := fun _ => inferInstance
  head := rfl
  last := Subsingleton.elim _ _
  step := fun i => Fin.elim0 i
  chief := fun i => Fin.elim0 i

private theorem exists_minimalNormal
    (D : Type) [Group D] [Finite D] [Nontrivial D] :
    ∃ M : Subgroup D, IsMinimalNormalSubgroup M := by
  let good : Subgroup D → Prop := fun M => M.Normal ∧ M ≠ ⊥
  have htop : (⊤ : Subgroup D) ≠ ⊥ := by
    exact top_ne_bot
  obtain ⟨M, hMtop, hM⟩ :=
    Finite.exists_le_minimal (p := good) (a := (⊤ : Subgroup D))
      ⟨inferInstance, htop⟩
  refine ⟨M, ⟨hM.1.1, hM.1.2, ?_⟩⟩
  intro K hKn hKne hKM
  exact hM.eq_of_le ⟨hKn, hKne⟩ hKM

/-- A whole-source elementary step preserves ordinary generation. -/
theorem genRank_le_compressed_add_capacity [Finite Q]
    (S : WreathState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (C : ElementaryMinimalNormalChart phi.ker)
    {H : ℕ} (hH : normalGen (K S phi) ≤ H) :
    genRank S.A ≤ genRank (S.quotient D' phi).A + H := by
  let E := E S phi C
  letI : IsMulCommutative (K S phi) := ⟨⟨fun a b =>
    E.equiv.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  let f := QuotientGroup.mk' (K S phi)
  letI : IsMulCommutative f.ker := by
    dsimp [f]
    rw [QuotientGroup.ker_mk']
    infer_instance
  have h := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    f (QuotientGroup.mk'_surjective _)
  have h' : genRank S.A ≤ genRank (S.quotient D' phi).A + normalGen (K S phi) := by
    simpa only [f, QuotientGroup.ker_mk', WreathState.quotient] using h
  exact h'.trans (Nat.add_le_add_left hH _)

/-- The literal local-chief trace bounds ordinary generators of the whole
source by generators of its retained top plus the induced cost times an
actual abelian chief length of the local component. -/
theorem exists_chief_ordinary_generator_bound [Finite Q]
    (hTracey : TraceyRefinedInducedModuleInput)
    (hs : 2 ≤ Fintype.card I)
    (S : WreathState Q I) [IsSolvable S.D] :
    ∃ c : ActualChiefSeries S.D,
      genRank S.A ≤ genRank Q + traceyInducedGeneratorCeiling 1 (Fintype.card I) *
        actualChiefSeriesAbelianLength c := by
  have hmain : ∀ n : ℕ, ∀ T : WreathState Q I,
      IsSolvable T.D → Nat.card T.D = n →
      ∃ c : ActualChiefSeries T.D,
        genRank T.A ≤ genRank Q +
          traceyInducedGeneratorCeiling 1 (Fintype.card I) *
            actualChiefSeriesAbelianLength c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hsol hcard
      letI : IsSolvable T.D := hsol
      rcases subsingleton_or_nontrivial T.D with ht | ht
      · letI : Subsingleton T.D := ht
        refine ⟨trivialChiefSeries T.D, ?_⟩
        simpa [actualChiefSeriesAbelianLength, trivialChiefSeries] using
          T.genRank_le_top
      · letI : Nontrivial T.D := ht
        obtain ⟨M, hM⟩ := exists_minimalNormal T.D
        letI : M.Normal := hM.1
        let D' := T.D ⧸ M
        let phi : T.D →* D' := QuotientGroup.mk' M
        have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective M
        have hker : phi.ker = M := QuotientGroup.ker_mk' M
        have hkerne : phi.ker ≠ ⊥ := by simpa [hker] using hM.2.1
        have hmin : ∀ K : Subgroup T.D, K.Normal → K ≤ phi.ker →
            K = ⊥ ∨ K = phi.ker := by
          intro K hKn hKM
          by_cases hK : K = ⊥
          · exact Or.inl hK
          · right
            exact (hM.2.2 K hKn hK (by simpa [hker] using hKM)).trans hker.symm
        have hcomm : IsMulCommutative phi.ker := by
          rw [hker]
          exact minimalNormal_isMulCommutative_of_isSolvable M hM
        obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty
          phi.ker hkerne hcomm hmin
        have hquot : Nat.card D' < Nat.card T.D := by
          rw [← M.index_eq_card, ← M.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [M.index_eq_card]; exact Nat.card_pos)
            (M.one_lt_card_iff_ne_bot.mpr hM.2.1)
        let T' := T.quotient D' phi
        obtain ⟨c, hc⟩ := ih (Nat.card D') (by omega) T'
          (show IsSolvable D' by infer_instance) rfl
        obtain ⟨H, hb, hH⟩ := exists_kernel_normalGen_bound T phi C
          hTracey hs (Classical.choice (inferInstance : Nonempty I))
        have hcost : H ≤ Module.finrank (ZMod C.p) C.V *
            traceyInducedGeneratorCeiling 1 (Fintype.card I) := by
          have hlog : H ≤ traceyInducedGeneratorCeiling
              (Module.finrank (ZMod C.p) C.V) (Fintype.card I) := by
            exact_mod_cast hb.logarithmic
          exact hlog.trans (traceyInducedGeneratorCeiling_le_mul _ _)
        have hminM : ∀ K : Subgroup T.D, K.Normal → K ≤ M → K = ⊥ ∨ K = M := by
          intro K hKn hKM
          by_cases hK : K = ⊥
          · exact Or.inl hK
          · exact Or.inr (hM.2.2 K hKn hK hKM)
        let c' := prependMinimalNormalChiefSeries M hM.2.1 hminM c
        have hlen : actualChiefSeriesAbelianLength c' =
            Module.finrank (ZMod C.p) C.V + actualChiefSeriesAbelianLength c := by
          rw [prependMinimalNormalChiefSeries_abelianLength]
          congr 1
          calc
            chiefAbelianLength M = chiefAbelianLength phi.ker :=
              chiefAbelianLength_congr (MulEquiv.subgroupCongr hker.symm)
            _ = Module.finrank (ZMod C.p) C.V := chiefAbelianLength_elementary C.equiv
        refine ⟨c', ?_⟩
        have hstep := genRank_le_compressed_add_capacity T phi C hH
        rw [hlen]
        calc
          genRank T.A ≤ genRank T'.A + H := hstep
          _ ≤ (genRank Q + traceyInducedGeneratorCeiling 1 (Fintype.card I) *
              actualChiefSeriesAbelianLength c) +
                Module.finrank (ZMod C.p) C.V *
                  traceyInducedGeneratorCeiling 1 (Fintype.card I) :=
            Nat.add_le_add hc hcost
          _ = genRank Q + traceyInducedGeneratorCeiling 1 (Fintype.card I) *
              (Module.finrank (ZMod C.p) C.V + actualChiefSeriesAbelianLength c) := by ring
  exact hmain (Nat.card S.D) S inferInstance rfl

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
