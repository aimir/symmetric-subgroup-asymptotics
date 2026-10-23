import SymmetricSubgroupAsymptotics.PrimeTopBlockReachability
import SymmetricSubgroupAsymptotics.BlockOrbitCentralizerCard
import SymmetricSubgroupAsymptotics.PrimeIndexUniformCentralizerClassBound
import SymmetricSubgroupAsymptotics.PermutationBlockClassReduction

/-! Prime-top coupled fusion for arbitrary original block kernels.
Component budgets control all actual coordinate subgroups. Outside
centralizers are detected on one original fibre by genuine powers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimeTopPermutationClassFusion
open OriginalBlockClassBound PrimeIndexAbelianCentralizers PrimeTopBlockReachability
    BlockOrbitCentralizerCard
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
    (b:Ω→X) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem outside_fixedKernel_card_le_factorial (x₀:X) (a p:ℕ) (hp:p.Prime)
    (htop:Nat.card (Top (A:=A) (X:=X))=p)
    (hsize:Nat.card (originalBlockFibre b x₀)≤a)
    (g:A) (hg:g∉Kernel (A:=A) (X:=X)) :
    Nat.card (fixedKernel (Kernel (A:=A) (X:=X)) g)≤a.factorial := by
  let r : Fin 1→X := fun _=>x₀
  have hreach : ∀ω:Ω,∃j:ℤ,∃i:Fin 1,b ((g^j)•ω)=r i := by
    intro ω
    obtain ⟨j,hj⟩ := outside_power_reaches_fibre b hb p hp htop g hg ω x₀
    exact ⟨j,0,hj⟩
  have h := fixedKernel_card_le_orbit_product b hb g r hreach
  have hprod : (∏i:Fin 1,(Nat.card (originalBlockFibre b (r i))).factorial)=
      (Nat.card (originalBlockFibre b x₀)).factorial := by simp [r]
  rw [hprod] at h
  exact h.trans (Nat.factorial_le hsize)

include hb in
theorem prime_top_class_bound (x₀:X) (a c p:ℕ) (hp:p.Prime)
    (htop:Nat.card (Top (A:=A) (X:=X))=p)
    (hsize:Nat.card (originalBlockFibre b x₀)≤a)
    (hc:∀x (L:Subgroup (Equiv.Perm (originalBlockFibre b x))),Nat.card (ConjClasses L)≤c) :
    p*Nat.card (ConjClasses A)+a.factorial≤c^Nat.card X+p^2*a.factorial := by
  letI : Fintype X := Fintype.ofFinite _
  have hk : Nat.card (ConjClasses (Kernel (A:=A) (X:=X)))≤c^Nat.card X := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using
      PermutationBlockClassReduction.kernel_class_card_le_product b hb (fun _=>c) hc
  have h := PrimeIndexUniformCentralizerClassBound.index_mul_class_card_le
    (Kernel (A:=A) (X:=X)) p hp
    ((Subgroup.index_ker (topMap (A:=A) (X:=X))).trans htop) a.factorial
    (outside_fixedKernel_card_le_factorial b hb x₀ a p hp htop hsize)
  exact h.trans (Nat.add_le_add_right hk _)

end SymmetricSubgroupAsymptotics.PrimeTopPermutationClassFusion
