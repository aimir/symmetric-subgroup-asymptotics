import SymmetricSubgroupAsymptotics.BinaryLinearQuadraticDichotomy
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Square-zero operators have image inside kernel. Two independent
image vectors supply four independent vectors and, in dimension four,
an actual basis of two difference-orbits. These are all-field linear
statements, with no Jordan form or finite matrix enumeration. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SquareZeroLinearBasisPairs

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem range_le_ker (N : V →ₗ[K] V) (hN : ∀v : V, N (N v)=0) :
    N.range ≤ N.ker := by
  rintro w ⟨v,rfl⟩
  exact hN v

theorem twice_range_finrank_le [FiniteDimensional K V]
    (N : V →ₗ[K] V) (hN : ∀v : V, N (N v)=0) :
    2*Module.finrank K N.range ≤ Module.finrank K V := by
  have hm := Submodule.finrank_mono (range_le_ker N hN)
  have hs := N.finrank_range_add_finrank_ker
  omega

theorem four_independent_of_independent_images
    (N : V →ₗ[K] V) (hN : ∀v : V, N (N v)=0) (v u : V)
    (hvu : LinearIndependent K ![N v,N u]) :
    LinearIndependent K ![v,N v,u,N u] := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hrel : a 0 • v+a 1 • N v+a 2 • u+a 3 • N u=0 := by
    simpa only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] using ha
  have hNrel : a 0 • N v+a 2 • N u=0 := by
    have hh := congrArg N hrel
    simpa only [map_add, map_smul, hN v, hN u, smul_zero,
      add_zero, zero_add, map_zero] using hh
  obtain ⟨ha0,ha2⟩ := LinearIndependent.pair_iff.mp hvu _ _ hNrel
  have hrel' : a 1 • N v+a 3 • N u=0 := by
    simpa only [ha0, ha2, zero_smul, zero_add, add_zero] using hrel
  obtain ⟨ha1,ha3⟩ := LinearIndependent.pair_iff.mp hvu _ _ hrel'
  intro i
  fin_cases i <;> simp_all

theorem exists_basis_difference_pairs [FiniteDimensional K V]
    (N : V →ₗ[K] V) (hN : ∀v : V, N (N v)=0)
    (hr : Module.finrank K N.range=2) (hd : Module.finrank K V=4)
    (e : V ≃ₗ[K] V) (he : ∀v : V, e v=v+N v) :
    ∃b : Module.Basis (Fin 4) K V,
      e (b 0)=b 0+b 1 ∧ e (b 2)=b 2+b 3 := by
  let c : Module.Basis (Fin 2) K N.range := Module.finBasisOfFinrankEq K N.range hr
  obtain ⟨v,hv⟩ := (c 0).property
  obtain ⟨u,hu⟩ := (c 1).property
  have hci := c.linearIndependent.map' N.range.subtype N.range.ker_subtype
  have hcf : (fun i : Fin 2 => ((c i : N.range) : V))=![N v,N u] := by
    ext i
    fin_cases i
    · exact hv.symm
    · exact hu.symm
  change LinearIndependent K (fun i : Fin 2 => ((c i : N.range) : V)) at hci
  rw [hcf] at hci
  have hfour := four_independent_of_independent_images N hN v u hci
  let b := basisOfLinearIndependentOfCardEqFinrank' ![v,N v,u,N u] hfour
    (by simpa only [Fintype.card_fin] using hd.symm)
  refine ⟨b, ?_, ?_⟩ <;>
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    exact he _

end SymmetricSubgroupAsymptotics.SquareZeroLinearBasisPairs
