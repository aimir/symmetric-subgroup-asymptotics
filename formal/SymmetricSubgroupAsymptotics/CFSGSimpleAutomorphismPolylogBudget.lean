import SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank
import SymmetricSubgroupAsymptotics.CFSGFiniteFamilyGeneration

/-! One uniform actual simple-factor rank/automorphism budget. Infinite
families use proved source generators and proper-index geometry; the
finite residual menu uses its genuine finite generation constant. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget
open PrimitiveSocleRawStructure CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

private theorem finite_simple_rank {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (j : Option CFSG.Sporadic)
    (e : D.Simple ≃* finiteModel j) :
    MarkedC4.genRank D.Simple≤CFSGGeneration.familyGenerationDegree finiteModel := by
  letI : Finite (finiteModel j) := Finite.of_equiv D.Simple e.toEquiv
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.family_generators finiteModel j
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact (MarkedC4.genRank_le hS).trans hcard

private theorem remaining_simple_rank {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (i : CFSG.Index)
    (hi : RemainingModel i) (e : D.Simple ≃* i.Model) :
    MarkedC4.genRank D.Simple≤CFSGGeneration.familyGenerationDegree finiteModel := by
  cases i <;> try { exact hi.elim }
  case tits => exact finite_simple_rank D none e
  case sporadic s => exact finite_simple_rank D (some s) e

theorem exists_uniform_simple_rank_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      MarkedC4.genRank D.Simple≤A*(Nat.log 2 ell+2)^2 := by
  let C := CFSGGeneration.familyGenerationDegree finiteModel
  refine ⟨C+32,?_⟩
  intro G X _ _ _ _ D ell hell
  obtain ⟨i,⟨e⟩⟩ := hCFSG.classify D.Simple
  rcases CFSGInfiniteSimplePolylogRank.simple_rank_or_remaining D i e ell hell with hr | hi
  · have h2 : 2≤ell := by
      obtain ⟨H,hH,he⟩ := hell.1
      have hh := H.one_lt_index_of_ne_top hH
      omega
    have hu := logb_le_natLog_add_one ell (by omega)
    have hL : 0≤Real.logb 2 (ell : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤ell by omega))
    have hs := (sq_le_sq₀ hL (by positivity : (0 : ℝ)≤(Nat.log 2 ell : ℝ)+1)).mpr hu
    have hl0 : (0 : ℝ)≤Nat.log 2 ell := by positivity
    have hc0 : (0 : ℝ)≤C := by positivity
    have hh : (MarkedC4.genRank D.Simple : ℝ)≤
        ((C+32 : ℕ) : ℝ)*((Nat.log 2 ell+2 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith only [hr,hs,hl0,hc0,
        mul_nonneg hc0 (sq_nonneg ((Nat.log 2 ell : ℝ)+2))]
    exact_mod_cast hh
  · have hr := remaining_simple_rank D i hi e
    have hb : C≤(C+32)*(Nat.log 2 ell+2)^2 := by
      nlinarith only [Nat.zero_le C,Nat.zero_le (Nat.log 2 ell),
        Nat.zero_le (C*(Nat.log 2 ell)^2),Nat.zero_le (C*Nat.log 2 ell)]
    exact hr.trans hb

theorem exists_uniform_automorphism_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell),
      Nat.card (D.Simple ≃* D.Simple)≤
        Nat.card D.Simple^(A*(Nat.log 2 ell+2)^2) := by
  obtain ⟨A,hA⟩ := exists_uniform_simple_rank_budget hCFSG
  refine ⟨A,?_⟩
  intro G X _ _ _ _ D ell hell
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := D.Simple)
  exact CFSGGeneration.aut_card_le_pow_of_generators S hS (hcard.le.trans (hA D ell hell))

end SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget
