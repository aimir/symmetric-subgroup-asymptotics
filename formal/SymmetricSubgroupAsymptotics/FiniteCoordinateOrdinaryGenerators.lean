import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-! Ordinary generator budgets for correlated finite coordinates. The
source is filtered by its actual coordinate kernels and quotient images.
Only ordinary extension subadditivity is used; no normal-generator
number is substituted for an ordinary generator number. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteCoordinateOrdinaryGenerators

/-- Actual jointly injective coordinate maps give an additive ordinary
rank budget over bounds for all actual coordinate subgroups. -/
theorem genRank_le_coordinate_sum (n : ℕ)
    (V : Fin n → Type) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : Fin n → ℕ) (hc : ∀i (L : Subgroup (V i)),MarkedC4.genRank L ≤ c i)
    (H : Type) [Group H] [Finite H] (f : ∀i,H→*V i)
    (hf : Function.Injective (fun h i=>f i h)) :
    MarkedC4.genRank H ≤ ∑i,c i := by
  induction n generalizing H with
  | zero =>
    letI : Subsingleton H := ⟨fun x y=>hf (funext fun i=>Fin.elim0 i)⟩
    have hgen : Subgroup.closure ((∅:Finset H):Set H)=⊤ := by
      rw [Finset.coe_empty,Subgroup.closure_empty]
      apply top_unique
      intro h _
      change h=1
      exact Subsingleton.elim _ _
    simpa only [Finset.card_empty,Fin.sum_univ_zero] using MarkedC4.genRank_le hgen
  | succ n ih =>
    let K := (f 0).ker
    let tail : ∀i:Fin n,K→*V i.succ := fun i=>(f i.succ).comp K.subtype
    have htail : Function.Injective (fun x i=>tail i x) := by
      intro x y he
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · exact x.property.trans y.property.symm
      · exact congrFun he j
    have hrec := ih (fun i:Fin n=>V i.succ) (fun i=>c i.succ)
      (fun i=>hc i.succ) K tail htail
    let e : H⧸K≃*(f 0).range := QuotientGroup.quotientKerEquivRange (f 0)
    have hquot : MarkedC4.genRank (H⧸K) ≤ c 0 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
      exact hc 0 (f 0).range
    rw [Fin.sum_univ_succ]
    exact (MarkedC4.genRank_le_of_normal K).trans
      ((Nat.add_le_add hrec hquot).trans_eq (Nat.add_comm _ _))

/-- The same argument indexed by an arbitrary finite original fibre set. -/
theorem genRank_le_finite_coordinate_sum {ι : Type} [Fintype ι]
    (V : ι→Type) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : ι→ℕ) (hc : ∀i (L : Subgroup (V i)),MarkedC4.genRank L ≤ c i)
    (H : Type) [Group H] [Finite H] (f : ∀i,H→*V i)
    (hf : Function.Injective (fun h i=>f i h)) :
    MarkedC4.genRank H ≤ ∑i,c i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun h j=>f (e j) h) := by
    intro x y he
    apply hf
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun he j
  have h := genRank_le_coordinate_sum (Fintype.card ι)
    (fun j=>V (e j)) (fun j=>c (e j)) (fun j=>hc (e j)) H (fun j=>f (e j)) hi
  simpa only [e.sum_comp] using h

theorem exists_generating_finset {ι : Type} [Fintype ι]
    (V : ι→Type) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : ι→ℕ) (hc : ∀i (L : Subgroup (V i)),MarkedC4.genRank L ≤ c i)
    (H : Type) [Group H] [Finite H] (f : ∀i,H→*V i)
    (hf : Function.Injective (fun h i=>f i h)) :
    ∃S:Finset H,Subgroup.closure (S:Set H)=⊤ ∧ S.card ≤ ∑i,c i := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=H)
  exact ⟨S,hgen,hS.le.trans (genRank_le_finite_coordinate_sum V c hc H f hf)⟩

end SymmetricSubgroupAsymptotics.FiniteCoordinateOrdinaryGenerators
