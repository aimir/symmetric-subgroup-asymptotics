import SymmetricSubgroupAsymptotics.ActualWreathElementaryOrdinaryStep
import SymmetricSubgroupAsymptotics.MinimalNormalChartOrdinaryGenerators
import SymmetricSubgroupAsymptotics.WreathNonabelianChiefOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular

/-! A genuine ordinary-generator recurrence along actual local chief
compressions. Every next state is the existing faithful compressed quotient.
Elementary costs are computed least induced capacities; nonabelian costs
are genuine ranks of selected internal simple factors. The relation stores
the actual finite trace, never an assumed numerical rank inequality.
No Tracey/MN input, simple two-generation, or nonabelian '+1' is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathOrdinaryChiefRecurrence
open PermutationalWreathProduct

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

/-- A computed cost of an actual finite local-chief trace at one original
block. No constructor accepts the desired ordinary-generation inequality. -/
inductive ChiefCost (i : I) : ActualWreathCompressionState Q I → ℕ → Prop where
  | terminal (S : ActualWreathCompressionState Q I) (hD : Subsingleton S.D) :
      ChiefCost i S 0
  | vanishing (S : ActualWreathCompressionState Q I)
      (D' : Type) [groupD' : Group D'] [finiteD' : Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (hmin : IsMinimalNormalSubgroup phi.ker)
      (hz : Compression.kernel S.rho phi = ⊥) (n : ℕ)
      (next : ChiefCost i (S.quotient D' phi hphi) n) :
      ChiefCost i S n
  | elementary (S : ActualWreathCompressionState Q I)
      (D' : Type) [groupD' : Group D'] [finiteD' : Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (hmin : IsMinimalNormalSubgroup phi.ker)
      (C : ElementaryMinimalNormalChart phi.ker) (n : ℕ)
      (next : ChiefCost i (S.quotient D' phi hphi) n) :
      ChiefCost i S (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i + n)
  | nonabelian (S : ActualWreathCompressionState Q I)
      (D' : Type) [groupD' : Group D'] [finiteD' : Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (hmin : IsMinimalNormalSubgroup phi.ker) (hnc : ¬ IsMulCommutative phi.ker)
      (hne : Compression.kernel S.rho phi ≠ ⊥)
      (C : SemisimpleNormalChart (Compression.kernel S.rho phi)) (j : C.ι) (n : ℕ)
      (next : ChiefCost i (S.quotient D' phi hphi) n) :
      ChiefCost i S (MarkedC4.genRank (C.factor j) + n)

private theorem terminal_rank (S : ActualWreathCompressionState Q I)
    (hD : Subsingleton S.D) : MarkedC4.genRank S.A ≤ MarkedC4.genRank Q := by
  letI : Subsingleton S.D := hD
  let f : S.A →* Q := rightHom.comp S.rho
  have hf : Function.Injective f := by
    intro a b hab
    apply S.rho_injective
    apply PermutationalWreathProduct.ext
    · funext j
      exact Subsingleton.elim _ _
    · exact hab
  letI : Finite Q := Finite.of_surjective f S.top_surjective
  let e : S.A ≃* Q := MulEquiv.ofBijective f ⟨hf, S.top_surjective⟩
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le

private theorem vanishing_rank (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (hphi : Function.Surjective phi)
    (hz : Compression.kernel S.rho phi = ⊥) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank (S.quotient D' phi hphi).A := by
  let E := Compression.kernel S.rho phi
  let f : S.A →* S.A ⧸ E := QuotientGroup.mk' E
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    ((QuotientGroup.ker_mk' E).trans hz)
  let e := MulEquiv.ofBijective f ⟨hf, QuotientGroup.mk'_surjective E⟩
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le

/-- Every recorded actual trace gives an ordinary bound in its ORIGINAL
source, with only the genuine final top rank left over. -/
theorem genRank_le_cost_add_top {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ChiefCost i S n) : MarkedC4.genRank S.A ≤ n + MarkedC4.genRank Q := by
  induction h with
  | terminal S hD => simpa only [zero_add] using terminal_rank S hD
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact (vanishing_rank S phi hphi hz).trans ih
  | elementary S D' phi hphi hmin C n next ih =>
      have hh := ActualWreathElementaryOrdinaryStep.genRank_le_capacity_add_next S phi C hphi i
      exact hh.trans ((Nat.add_le_add_left ih _).trans_eq (Nat.add_assoc _ _ _).symm)
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      letI : MulAction.IsPretransitive Q I := S.top_pretransitive
      have hminimal := WreathNonabelianChiefOrdinaryStep.minimalNormal_kernel
        S.rho phi S.rho_injective S.top_surjective S.fullComponent hmin hnc hne
      have hh := MinimalNormalChartOrdinaryGenerators.genRank_le_factor
        (Compression.kernel S.rho phi) hminimal C j
      exact hh.trans ((Nat.add_le_add_left ih _).trans_eq (Nat.add_assoc _ _ _).symm)

/-- Existence is obtained by decreasing the order of the literal local
component. All elementary capacities and all simple-factor charts are
proved constructions, not extra published hypotheses. -/
theorem exists_chiefCost (i : I) (S : ActualWreathCompressionState Q I) :
    ∃ n : ℕ, ChiefCost i S n := by
  classical
  have main : ∀ m : ℕ, ∀ T : ActualWreathCompressionState Q I,
      Nat.card T.D = m → ∃ n : ℕ, ChiefCost i T n := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hcard
      rcases subsingleton_or_nontrivial T.D with hsub | hnontrivial
      · exact ⟨0, .terminal T hsub⟩
      · letI : Nontrivial T.D := hnontrivial
        obtain ⟨L, hL⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := T.D)
        letI : L.Normal := hL.1
        let D' := T.D ⧸ L
        let phi : T.D →* D' := QuotientGroup.mk' L
        have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective L
        have hker : phi.ker = L := QuotientGroup.ker_mk' L
        have hmin : IsMinimalNormalSubgroup phi.ker := by rw [hker]; exact hL
        have hsmall : Nat.card D' < Nat.card T.D := by
          rw [← L.index_eq_card, ← L.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [L.index_eq_card]; exact Nat.card_pos)
            (L.one_lt_card_iff_ne_bot.mpr hL.2.1)
        obtain ⟨n, hn⟩ := ih (Nat.card D') (by omega)
          (T.quotient D' phi hphi) rfl
        by_cases hz : Compression.kernel T.rho phi = ⊥
        · exact ⟨n, .vanishing T D' phi hphi hmin hz n hn⟩
        · have hlocal (K : Subgroup T.D) (hK : K.Normal) (hle : K ≤ phi.ker) :
              K = ⊥ ∨ K = phi.ker := by
            by_cases hzero : K = ⊥
            · exact Or.inl hzero
            · exact Or.inr (hmin.2.2 K hK hzero hle)
          by_cases hc : IsMulCommutative phi.ker
          · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty phi.ker hmin.2.1 hc hlocal
            exact ⟨_, .elementary T D' phi hphi hmin C n hn⟩
          · let C0 := semisimpleNormalChart_of_nonabelian_minimal phi.ker hlocal hc
            let C := Compression.kernelSemisimpleChartOfFullComponent
              T.rho phi T.rho_injective T.fullComponent C0
            have hindex : Nonempty C.ι := by
              by_contra hnone
              apply hz
              apply bot_unique
              intro a ha
              have he : (⟨a, ha⟩ : Compression.kernel T.rho phi) = 1 := by
                apply C.equiv.injective
                funext j
                exact False.elim (hnone ⟨j⟩)
              exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)
            let j : C.ι := Classical.choice hindex
            exact ⟨_, .nonabelian T D' phi hphi hmin hc hz C j n hn⟩
  exact main (Nat.card S.D) S rfl

/-- A finite set of actual original generators, paid by one actual
chief trace and the actual block-top rank. -/
theorem exists_generating_finset (i : I) (S : ActualWreathCompressionState Q I) :
    ∃ n : ℕ, ChiefCost i S n ∧ ∃ F : Finset S.A,
      Subgroup.closure (F : Set S.A) = ⊤ ∧ F.card ≤ n + MarkedC4.genRank Q := by
  obtain ⟨n, hn⟩ := exists_chiefCost i S
  obtain ⟨F, hcard, hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨n, hn, F, hgen, hcard.le.trans (genRank_le_cost_add_top hn)⟩

end SymmetricSubgroupAsymptotics.ActualWreathOrdinaryChiefRecurrence
