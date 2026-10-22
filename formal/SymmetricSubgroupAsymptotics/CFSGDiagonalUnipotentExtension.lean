import SymmetricSubgroupAsymptotics.CFSGMatrixFlagPowerDiagonal
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSoluble
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.GroupTheory.PGroup

/-! An actual unitriangular subgroup extended by arbitrary diagonal units.
The extension is soluble and every defining-characteristic power element
belongs to the unitriangular subgroup; the diagonal need not lie in a named
torus. No finite-group order formula is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalUnipotentExtension
variable {I K : Type} [Fintype I] [DecidableEq I] [Field K] {m : ℕ}

private theorem triangular_of_isDiag (e : I≃Fin m) (d : (Matrix I I K)ˣ)
    (hd : (d : Matrix I I K).IsDiag) : (d : Matrix I I K).BlockTriangular e := by
  rw [←hd.diagonal_diag]
  exact Matrix.blockTriangular_diagonal _

theorem power_element_mem (e : I≃Fin m) (U : Subgroup ((Matrix I I K)ˣ))
    (hU : U≤CFSGMatrixFlagSubgroups.unipotentUnits e)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : (Matrix I I K)ˣ) (k : ℕ) (hk : g^(p^k)=1)
    (hfactor : ∃u∈U,∃d : (Matrix I I K)ˣ,(d : Matrix I I K).IsDiag ∧ g=u*d) : g∈U := by
  obtain ⟨u,hu,d,hd,hg⟩ := hfactor
  have hu' := hU hu
  have hdtri := triangular_of_isDiag e d hd
  have hgtri : (g : Matrix I I K).BlockTriangular e := by
    rw [hg,Units.val_mul]
    exact hu'.1.mul hdtri
  have hpow : (g : Matrix I I K)^(p^k)=1 := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using
      congrArg (fun x : (Matrix I I K)ˣ=>(x : Matrix I I K)) hk
  have hd1 : ∀i : I,(d : Matrix I I K) i i=1 := by
    intro i
    have hi := CFSGMatrixFlagSubgroups.diagonal_one_of_prime_power e p
      (g : Matrix I I K) hgtri k hpow i
    rw [hg,Units.val_mul,CFSGMatrixFlagSubgroups.upper_diag_mul e hu'.1 hdtri,
      hu'.2 i,one_mul] at hi
    exact hi
  have he : d=1 := by
    apply Units.ext
    rw [←hd.diagonal_diag]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply,hd1]
  rw [he,mul_one] at hg
  exact hg.symm ▸ hu

theorem subgroup_soluble (e : I≃Fin m) (N U : Subgroup ((Matrix I I K)ˣ))
    (hU : U≤CFSGMatrixFlagSubgroups.unipotentUnits e)
    (hfactor : ∀g∈N,∃u∈U,∃d : (Matrix I I K)ˣ,(d : Matrix I I K).IsDiag ∧ g=u*d) :
    IsSolvable N := by
  have hN : N≤CFSGMatrixFlagSubgroups.borelUnits e := by
    intro g hg
    obtain ⟨u,hu,d,hd,he⟩ := hfactor g hg
    change (g : Matrix I I K).BlockTriangular e
    rw [he,Units.val_mul]
    exact (hU hu).1.mul (triangular_of_isDiag e d hd)
  letI : IsSolvable (CFSGMatrixFlagSubgroups.borelUnits (K:=K) e) :=
    CFSGMatrixFlagSubgroups.borelUnits_soluble (K:=K) e
  exact solvable_of_solvable_injective (f:=Subgroup.inclusion hN)
    (Subgroup.inclusion_injective hN)

theorem pSubgroup_le (e : I≃Fin m) (N U P : Subgroup ((Matrix I I K)ˣ))
    (hU : U≤CFSGMatrixFlagSubgroups.unipotentUnits e)
    (hfactor : ∀g∈N,∃u∈U,∃d : (Matrix I I K)ˣ,(d : Matrix I I K).IsDiag ∧ g=u*d)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hP : IsPGroup p P) (hPN : P≤N) : P≤U := by
  intro g hg
  obtain ⟨k,hk⟩ := hP ⟨g,hg⟩
  have hpow : g^(p^k)=1 := congrArg P.subtype hk
  exact power_element_mem e U hU p g k hpow (hfactor g (hPN hg))

end SymmetricSubgroupAsymptotics.CFSGDiagonalUnipotentExtension
