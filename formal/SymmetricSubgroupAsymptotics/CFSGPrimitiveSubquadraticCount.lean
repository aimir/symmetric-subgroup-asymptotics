import SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitiveSubquadraticCount
import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! ALL literal labelled primitive subgroups have weak subquadratic count
from CFSG. The affine branch uses its proved logarithmic-square rank bound;
the nonaffine branch uses the actual full-socle uniform family bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveSubquadraticCount
open PrimitiveSocleRawStructure

theorem exists_uniform_rank_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X],
      MarkedC4.genRank G ≤ A*(Nat.log 2 (Nat.card X)+2)^2 := by
  obtain ⟨A,hA⟩ := CFSGNonaffinePrimitivePolylogRank.exists_uniform_rank_budget hCFSG
  refine ⟨A+2,?_⟩
  intro G X _ _ _ _ _ _ hp
  obtain ⟨D | P⟩ := publishedONanScottStructure G X
  · exact (hA D).trans (Nat.mul_le_mul_right _ (by omega))
  · have hr := PrimitiveAffineCoarseOrdinaryTail.genRank_le_log_square_add_one P hp
    have hu := CFSGNonaffinePrimitivePolylogRank.logb_le_natLog_add_one
      (Nat.card X) (Nat.card_pos)
    have hl0 : (0 : ℝ)≤Nat.log 2 (Nat.card X) := by positivity
    have hL0 : 0≤Real.logb 2 (Nat.card X : ℝ) := by
      apply Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
      exact_mod_cast (show 1≤Nat.card X from Nat.card_pos)
    have hs := (sq_le_sq₀ hL0 (by positivity :
      (0 : ℝ)≤(Nat.log 2 (Nat.card X) : ℝ)+1)).mpr hu
    have hA0 : (0 : ℝ)≤A := by positivity
    have hh : (MarkedC4.genRank G : ℝ)≤
        ((A+2 : ℕ) : ℝ)*((Nat.log 2 (Nat.card X)+2 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith only [hr,hs,hl0,hA0,
        mul_nonneg hA0 (sq_nonneg ((Nat.log 2 (Nat.card X) : ℝ)+2))]
    exact_mod_cast hh

abbrev Sector (n : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin n)) // MulAction.IsPreprimitive H (Fin n)}

local instance (n : ℕ) : Fintype (Sector n) := Fintype.ofFinite _

theorem exists_uniform_count_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ n : ℕ,2≤n →
      Nat.card (Sector n)≤n.factorial^(A*(Nat.log 2 n+2)^2) := by
  obtain ⟨A,hA⟩ := exists_uniform_rank_budget hCFSG
  refine ⟨A,?_⟩
  intro n hn
  let B := A*(Nat.log 2 n+2)^2
  have hr : ∀ H : Sector n,MarkedC4.genRank H.val≤B := by
    intro H
    letI := H.property
    letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1<n by omega))
    simpa only [Nat.card_fin] using hA (G := H.val) (X := Fin n)
  let f : Sector n → {H : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank H≤B} :=
    fun H => ⟨H.val,hr H⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg
      (fun a : {U : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank U≤B} => a.val) h)
  have hh := (Nat.card_le_card_of_injective f hf).trans
    (FiniteSubgroupSmallOrderCount.card_rank_bounded_subgroups_le
      (G := Equiv.Perm (Fin n)) B)
  simpa only [Nat.card_perm,Nat.card_fin,B] using hh

theorem sector_subquadratic (hCFSG : CFSG.CFSGClassification) :
    SubquadraticMenuIndexCount Sector := by
  obtain ⟨A,hA⟩ := exists_uniform_count_budget hCFSG
  exact FactorialUniformPolylogSubquadraticCount.subquadratic_of_factorial_budget A hA

end SymmetricSubgroupAsymptotics.CFSGPrimitiveSubquadraticCount
