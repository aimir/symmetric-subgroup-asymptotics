import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Lean.Elab.Tactic.Omega

/-! An actual nonidentity transvection admits original linear coordinates
in which its vector is the first standard basis vector and its form is
the last coordinate. Only an unrestricted linear change of basis is
needed, since it induces an automorphism of SL and its centre quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionBasis
open Module LinearMap
variable {F : Type*} [Field F] {n : ℕ}

theorem exists_highest_root_coordinates (hn : 2≤n)
    (f : Dual F (Fin n→F)) (v : Fin n→F) (hfv : f v=0) (hf : f≠0) (hv : v≠0) :
    ∃e : (Fin n→F)≃ₗ[F](Fin n→F),
      e v=Pi.single (⟨0,by omega⟩ : Fin n) 1 ∧
      ∀x : Fin n→F,f (e.symm x)=x ⟨n-1,by omega⟩ := by
  obtain ⟨ι,b,i,j,hij,hvb,hfb⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card ι=Fintype.card (Fin n) := by
    rw [←Module.finrank_eq_card_basis b,Module.finrank_fintype_fun_eq_card]
  let e0 : ι≃Fin n := Fintype.equivOfCardEq hcard
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hfl : first≠last := by intro he;have hh := congrArg Fin.val he;dsimp [first,last] at hh;omega
  have hp : MulAction.IsMultiplyPretransitive (Equiv.Perm (Fin n)) (Fin n) 2 :=
    Equiv.Perm.isMultiplyPretransitive _ _
  obtain ⟨σ,hσi,hσj⟩ := (MulAction.is_two_pretransitive_iff.mp hp) (e0.injective.ne hij) hfl
  change σ (e0 i)=first at hσi
  change σ (e0 j)=last at hσj
  let idx : ι≃Fin n := e0.trans σ
  have hri : idx.symm first=i := by
    apply idx.injective
    rw [idx.apply_symm_apply]
    exact hσi.symm
  have hrj : idx.symm last=j := by
    apply idx.injective
    rw [idx.apply_symm_apply]
    exact hσj.symm
  let c : Basis (Fin n) F (Fin n→F) := b.reindex idx
  have hvc : v=c first := by
    change v=(b.reindex idx) first
    rw [Basis.reindex_apply,hri]
    exact hvb
  have hfc : f=c.coord last := by
    rw [hfb]
    apply LinearMap.ext
    intro x
    change b.repr x j=(b.reindex idx).repr x last
    rw [Basis.repr_reindex_apply,hrj]
  refine ⟨c.equivFun,?_,?_⟩
  · rw [hvc]
    change c.equivFun (c first)=Pi.single first 1
    ext k
    simp only [Basis.equivFun_self,Pi.single_apply]
    simp only [eq_comm]
  · intro x
    rw [hfc]
    exact Basis.coord_equivFun_symm c last x

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionBasis
