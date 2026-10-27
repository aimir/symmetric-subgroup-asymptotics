import SymmetricSubgroupAsymptotics.CFSGInfiniteSimplePolylogRank
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A uniform actual nonaffine primitive rank budget from CFSG alone.
The finite menu is absorbed by genuine finite constants, not by assuming
orders, displayed pairs or numerical outer callbacks. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open FiniteModelPrimitiveOrdinaryBudget

def finiteModel : Option CFSG.Sporadic → Type
  | none => CFSG.Models.Tits
  | some s => s.Model

instance (i : Option CFSG.Sporadic) : Group (finiteModel i) := by
  cases i <;> unfold finiteModel <;> infer_instance

private theorem remaining_budget (C : ℕ)
    (hC : ∀ i,HasModelBudget (finiteModel i) C)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X) (i : CFSG.Index) (hi : RemainingModel i)
    (e : D.Simple ≃* i.Model) :
    MarkedC4.genRank G ≤ (Nat.log 2 (Nat.card X)+2)*C+(Nat.log 2 (Nat.card X))^2 := by
  cases i <;> try { exact hi.elim }
  case tits => exact hC none D e
  case sporadic s => exact hC (some s) D e

theorem logb_le_natLog_add_one (n : ℕ) (hn : 0<n) :
    Real.logb 2 (n : ℝ) ≤ (Nat.log 2 n : ℝ)+1 := by
  have hh := IntegerLogSquareRootCeilingCertificate.log_upper n 1 (Nat.log 2 n+1)
    hn (by decide)
    (by simpa only [pow_one] using (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le)
  simpa only [Nat.cast_add,Nat.cast_one,div_one] using hh

theorem exists_uniform_rank_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
      (D : NonaffineData G X),
      MarkedC4.genRank G ≤ A*(Nat.log 2 (Nat.card X)+2)^2 := by
  obtain ⟨C,hC⟩ := finite_family_budget finiteModel
  refine ⟨C+32,?_⟩
  intro G X _ _ _ _ _ _ _ D
  let l := Nat.log 2 (Nat.card X)
  rcases CFSGInfiniteSimplePolylogRank.primitive_rank_or_actual_finite_model D hCFSG with hr | hr
  · have hnp : 0<Nat.card X := Nat.card_pos
    have hu := logb_le_natLog_add_one (Nat.card X) hnp
    have h2 : 2≤Nat.card X := by
      have hh : 1<Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    have hL : 1≤Real.logb 2 (Nat.card X : ℝ) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (by norm_num : (0 : ℝ)<2) (by exact_mod_cast h2 : (2 : ℝ)≤Nat.card X)
      simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
    have hl0 : (0 : ℝ)≤l := by positivity
    have hc0 : (0 : ℝ)≤C := by positivity
    have hs : (Real.logb 2 (Nat.card X : ℝ))^2≤((l : ℝ)+1)^2 :=
      (sq_le_sq₀ (by linarith) (by positivity)).mpr hu
    have hh : (MarkedC4.genRank G : ℝ)≤((C+32 : ℕ) : ℝ)*((l+2 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith only [hr,hu,hL,hs,hl0,hc0,
        mul_nonneg hc0 (sq_nonneg ((l : ℝ)+2))]
    exact_mod_cast hh
  · obtain ⟨i,hi,⟨e⟩⟩ := hr
    have hb := remaining_budget C hC D i hi e
    have hb' : (l+2)*C+l^2≤(C+32)*(l+2)^2 := by
      nlinarith only [Nat.zero_le C,Nat.zero_le l,Nat.zero_le (C*l*l),Nat.zero_le (C*l)]
    exact hb.trans hb'

end SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank
