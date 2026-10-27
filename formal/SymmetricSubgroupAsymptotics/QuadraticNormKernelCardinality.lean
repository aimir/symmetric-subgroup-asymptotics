import SymmetricSubgroupAsymptotics.QuadraticNormOneSpecialLinearEmbedding
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Norm-kernel cardinality for ANY genuine quadratic finite-field extension,
not just a selected abstract extension. The basis is actual coordinate data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuadraticNormKernelCardinality
open QuadraticNormOneSpecialLinearEmbedding
variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] [Finite K]

theorem norm_one_card (b : Module.Basis (Fin 2) F K) :
    Nat.card (NormOne F K)=Nat.card F+1 := by
  letI : Module.Finite F K := Module.Finite.of_basis b
  have hc : Nat.card K=(Nat.card F)^2 := by
    rw [Module.natCard_eq_pow_finrank (K:=F),Module.finrank_eq_card_basis b,Fintype.card_fin]
  let n := normUnits F K
  have hsurj : Function.Surjective n := FiniteField.unitsMap_norm_surjective F K
  have hm := n.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hsurj,Subgroup.card_top,
    Nat.card_units,Nat.card_units] at hm
  change Nat.card (NormOne F K)*(Nat.card F-1)=Nat.card K-1 at hm
  rw [hc] at hm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hsub : Nat.card F-1+1=Nat.card F := Nat.sub_add_cancel (by omega)
  have he : (Nat.card F+1)*(Nat.card F-1)=(Nat.card F)^2-1 := by
    have hpow : 1 ≤ (Nat.card F)^2 := by nlinarith
    have hs := Nat.sub_add_cancel hpow
    nlinarith
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0<Nat.card F-1)
  exact hm.trans he.symm

end SymmetricSubgroupAsymptotics.QuadraticNormKernelCardinality
