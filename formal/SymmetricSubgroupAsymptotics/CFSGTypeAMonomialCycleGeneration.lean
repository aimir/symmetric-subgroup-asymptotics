import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction
import SymmetricSubgroupAsymptotics.CFSGTypeACycleRootGeneration

/-! One full root group and an actual monomial lift of a spanning
coordinate cycle generate SL. The cycle moves both root indices, while
nonzero row weights are compensated in the scalar parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAMonomialCycleGeneration
open CFSGTypeAElementaryMatrices CFSGTypeAMonomialRootAction
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

theorem eq_top_of_full_edge (hn : 2≤Fintype.card n)
    (σ : Equiv.Perm n) (hσ : σ.IsCycleOn (Finset.univ : Finset n))
    (W : SL (n:=n) (F:=F)) (d : n→F)
    (hW : W.val=CFSGTypeAMonomialMatrices.monomial σ d) (hd : ∀ k,d k≠0)
    (H : Subgroup (SL (n:=n) (F:=F))) (hHW : W∈H)
    (i : n) (hi : i≠σ.symm i) (hRoot : ∀ a : F,elementary hi a∈H) : H=⊤ := by
  let τ : Equiv.Perm n := σ⁻¹
  have hτ : τ.IsCycleOn (Finset.univ : Finset n) := hσ.inv
  have hmove : ∀ j : n,j≠τ j := by
    intro j he
    have hdiv := (hτ.pow_apply_eq (Finset.mem_univ j)).mp
      (show (τ^1) j=j by simpa only [pow_one] using he.symm)
    rw [Finset.card_univ] at hdiv
    have hle := Nat.le_of_dvd (by decide : 0<1) hdiv
    omega
  have hOrbit : ∀ k : ℕ,∀ a : F,
      elementary (hmove ((τ^k) i)) a∈H := by
    intro k
    induction k with
    | zero => simpa only [pow_zero,Equiv.Perm.one_apply] using hRoot
    | succ k ih =>
      have ht := full_root_transfer H W hHW σ d hW hd (hmove ((τ^k) i)) ih
      have he : (τ^(k+1)) i=σ.symm ((τ^k) i) := by
        simp only [pow_succ',Equiv.Perm.mul_apply,τ,Equiv.Perm.inv_def]
      simpa only [he] using ht
  apply CFSGTypeACycleRootGeneration.eq_top_of_cycle_roots hn τ hτ H
  intro j hj a
  obtain ⟨k,_,hk⟩ := hτ.exists_pow_eq (Finset.mem_univ i) (Finset.mem_univ j)
  simpa only [hk] using hOrbit k a

end SymmetricSubgroupAsymptotics.CFSGTypeAMonomialCycleGeneration
