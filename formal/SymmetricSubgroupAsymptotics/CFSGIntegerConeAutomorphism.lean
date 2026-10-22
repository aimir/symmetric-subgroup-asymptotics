import Mathlib.Order.Cover
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Int.SuccPred
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic

/-! A lattice automorphism preserving the nonnegative coordinate cone
in both directions permutes the original coordinate simple vectors.
The argument uses the literal covers of zero in the integer product
order, so it does not assume Weyl-chamber recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegerConeAutomorphism
variable {I : Type*} [Fintype I] [DecidableEq I]

def coneOrderIso (e : (I→ℤ)≃+(I→ℤ))
    (he : ∀x : I→ℤ,0≤x→0≤e x)
    (hi : ∀x : I→ℤ,0≤x→0≤e.symm x) : (I→ℤ)≃o(I→ℤ) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have hh := hi (e y-e x) (sub_nonneg.mpr h)
      rw [map_sub,e.symm_apply_apply,e.symm_apply_apply] at hh
      exact sub_nonneg.mp hh
    · intro h
      have hh := he (y-x) (sub_nonneg.mpr h)
      rw [map_sub] at hh
      exact sub_nonneg.mp hh

theorem zero_covBy_single (i : I) : (0 : I→ℤ)⋖(Pi.single i 1 : I→ℤ) := by
  apply Pi.covBy_iff.mpr
  refine ⟨i,?_,?_⟩
  · simpa using (show (0:ℤ)⋖1 from by
      rw [Order.covBy_iff_add_one_eq]
      exact zero_add 1)
  · intro j hji
    simp [Pi.single_apply,hji,Ne.symm hji]

theorem maps_single (e : (I→ℤ)≃+(I→ℤ))
    (he : ∀x : I→ℤ,0≤x→0≤e x)
    (hi : ∀x : I→ℤ,0≤x→0≤e.symm x) (i : I) :
    ∃j : I,e (Pi.single i 1)=Pi.single j 1 := by
  have hc := (apply_covBy_apply_iff (coneOrderIso e he hi)).mpr (zero_covBy_single i)
  change e 0⋖e (Pi.single i 1) at hc
  rw [map_zero] at hc
  obtain ⟨j,hj,hrest⟩ := Pi.covBy_iff.mp hc
  have hjone : e (Pi.single i 1) j=1 := by
    change (0:ℤ)⋖e (Pi.single i 1) j at hj
    rw [Order.covBy_iff_add_one_eq] at hj
    simpa only [zero_add] using hj.symm
  refine ⟨j,?_⟩
  funext k
  by_cases hkj : k=j
  · subst k
    simpa using hjone
  · have hkzero : e (Pi.single i 1) k=0 := (hrest k hkj).symm
    simp [hkzero,Pi.single_apply,hkj,Ne.symm hkj]

theorem permutes_singles (e : (I→ℤ)≃+(I→ℤ))
    (he : ∀x : I→ℤ,0≤x→0≤e x)
    (hi : ∀x : I→ℤ,0≤x→0≤e.symm x) :
    ∃σ : Equiv.Perm I,∀i : I,e (Pi.single i 1)=Pi.single (σ i) 1 := by
  classical
  choose f hf using maps_single e he hi
  have hinj : Function.Injective f := by
    intro i j hij
    have hh : (Pi.single i 1 : I→ℤ)=Pi.single j 1 := by
      apply e.injective
      rw [hf,hf,hij]
    by_contra hne
    have hc := congrFun hh i
    simp [Pi.single_apply,hne,Ne.symm hne] at hc
  exact ⟨Equiv.ofBijective f ⟨hinj,Finite.injective_iff_surjective.mp hinj⟩,hf⟩

theorem maps_cone_of_simple_images (e : (I→ℤ)≃ₗ[ℤ](I→ℤ))
    (he : ∀i : I,0≤e (Pi.single i 1)) : ∀x : I→ℤ,0≤x→0≤e x := by
  intro x hx j
  have hsum : e x=∑i : I,x i • e (Pi.single i 1) := by
    conv_lhs=>rw [pi_eq_sum_univ' x]
    simp only [map_sum,map_smul]
  rw [hsum,Finset.sum_apply]
  apply Finset.sum_nonneg
  intro i _
  change 0≤x i*e (Pi.single i 1) j
  exact mul_nonneg (hx i) (he i j)

theorem permutes_singles_of_simple_images (e : (I→ℤ)≃ₗ[ℤ](I→ℤ))
    (he : ∀i : I,0≤e (Pi.single i 1))
    (hi : ∀i : I,0≤e.symm (Pi.single i 1)) :
    ∃σ : Equiv.Perm I,∀i : I,e (Pi.single i 1)=Pi.single (σ i) 1 :=
  permutes_singles e.toAddEquiv (maps_cone_of_simple_images e he)
    (maps_cone_of_simple_images e.symm hi)

end SymmetricSubgroupAsymptotics.CFSGIntegerConeAutomorphism
