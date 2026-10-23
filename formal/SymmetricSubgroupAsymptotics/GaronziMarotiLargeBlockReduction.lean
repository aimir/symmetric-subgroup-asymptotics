import SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The large-block induction step for the exact Garonzi--Maroti
class-number exponent. A literal faithful equivariant block action with
block size and block count at least four inherits the bound from ALL
smaller permutation degrees. The original correlated block kernel and
actual top image are retained. This is not a proof of the primitive
case or of the small block/top cases of sizes two and three. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
open OriginalBlockClassBound PermutationBlockClassReduction

theorem class_card_le_of_finite_permutation_bound (Y : Type) [Finite Y] (c : ℝ)
    (hbound : ∀L : Subgroup (Equiv.Perm (Fin (Nat.card Y))),
      (Nat.card (ConjClasses L):ℝ)≤c) (L : Subgroup (Equiv.Perm Y)) :
    (Nat.card (ConjClasses L):ℝ)≤c := by
  let e : Y≃Fin (Nat.card Y) := Finite.equivFinOfCardEq rfl
  let T : Subgroup (Equiv.Perm (Fin (Nat.card Y))) := L.map e.permCongrHom.toMonoidHom
  let a : L≃*T := e.permCongrHom.subgroupMap L
  have hn : Nat.card (ConjClasses L)≤Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)
  have hr : (Nat.card (ConjClasses L):ℝ)≤(Nat.card (ConjClasses T):ℝ) := by
    exact_mod_cast hn
  exact hr.trans (hbound T)

theorem card_eq_blocks_mul_fibre {Ω X : Type} [Finite Ω] [Finite X]
    (b : Ω→X) (k : ℕ) (hfibre : ∀x,Nat.card (originalBlockFibre b x)=k) :
    Nat.card Ω=Nat.card X*k := by
  letI : Fintype X := Fintype.ofFinite _
  calc
    Nat.card Ω=Nat.card ((x : X)×originalBlockFibre b x) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv b)).symm
    _=∑x : X,Nat.card (originalBlockFibre b x) := Nat.card_sigma
    _=Nat.card X*k := by simp only [hfibre,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,Nat.card_eq_fintype_card]

theorem exact_exponent_large_block_step {A Ω X : Type} [Group A]
    [Finite A] [Finite Ω] [Finite X] [MulAction A Ω] [MulAction A X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (k : ℕ)
    (hk : 4≤k) (hblocks : 4≤Nat.card X)
    (hfibre : ∀x,Nat.card (originalBlockFibre b x)=k)
    (hSmaller : ∀m : ℕ,m<Nat.card Ω→4≤m→
      ∀L : Subgroup (Equiv.Perm (Fin m)),
        (Nat.card (ConjClasses L):ℝ)≤(5:ℝ)^(((m:ℝ)-1)/3)) :
    (Nat.card (ConjClasses A):ℝ)≤(5:ℝ)^(((Nat.card Ω:ℝ)-1)/3) := by
  letI : Fintype X := Fintype.ofFinite _
  have hdegree := card_eq_blocks_mul_fibre b k hfibre
  have hklt : k<Nat.card Ω := by rw [hdegree]; nlinarith
  have hXlt : Nat.card X<Nat.card Ω := by rw [hdegree]; nlinarith
  have hlocal (x : X) (L : Subgroup (Equiv.Perm (originalBlockFibre b x))) :
      (Nat.card (ConjClasses L):ℝ)≤(5:ℝ)^(((k:ℝ)-1)/3) := by
    have hm : Nat.card (originalBlockFibre b x)<Nat.card Ω := by rwa [hfibre]
    have h4 : 4≤Nat.card (originalBlockFibre b x) := by rwa [hfibre]
    have hh := class_card_le_of_finite_permutation_bound (originalBlockFibre b x) _
      (hSmaller _ hm h4) L
    simpa only [hfibre] using hh
  have htop : (Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ)≤
      (5:ℝ)^(((Nat.card X:ℝ)-1)/3) :=
    class_card_le_of_finite_permutation_bound X _
      (hSmaller _ hXlt hblocks) (Top (A:=A) (X:=X))
  have hp : 0≤(5:ℝ)^(((k:ℝ)-1)/3) := Real.rpow_nonneg (by norm_num) _
  have hrec := real_class_card_le_product_mul_top b hb
    (fun _=>(5:ℝ)^(((k:ℝ)-1)/3)) (fun _=>hp) hlocal
  have hdegreeR : (Nat.card Ω:ℝ)=(Nat.card X:ℝ)*(k:ℝ) := by exact_mod_cast hdegree
  calc
    (Nat.card (ConjClasses A):ℝ)≤
        (∏_x : X,(5:ℝ)^(((k:ℝ)-1)/3))*
          (Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ) := hrec
    _≤(∏_x : X,(5:ℝ)^(((k:ℝ)-1)/3))*(5:ℝ)^(((Nat.card X:ℝ)-1)/3) :=
      mul_le_mul_of_nonneg_left htop (Finset.prod_nonneg (fun _ _=>hp))
    _=((5:ℝ)^(((k:ℝ)-1)/3))^(Nat.card X)*(5:ℝ)^(((Nat.card X:ℝ)-1)/3) := by
      simp only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]
    _=(5:ℝ)^((((k:ℝ)-1)/3)*(Nat.card X:ℝ)+((Nat.card X:ℝ)-1)/3) := by
      rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤5),←Real.rpow_add (by norm_num : (0:ℝ)<5)]
    _=(5:ℝ)^(((Nat.card Ω:ℝ)-1)/3) := by
      congr 1
      rw [hdegreeR]
      ring

end SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
