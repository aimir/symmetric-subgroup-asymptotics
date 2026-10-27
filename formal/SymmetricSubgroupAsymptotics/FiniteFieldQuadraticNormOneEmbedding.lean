import SymmetricSubgroupAsymptotics.QuadraticNormOneSpecialLinearEmbedding
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! A genuine quadratic finite-field extension supplies the basis and norm-one
group internally. Its actual SL2 multiplication image has exactly q+1 elements. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteFieldQuadraticNormOneEmbedding
open QuadraticNormOneSpecialLinearEmbedding
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

abbrev Quadratic := FiniteField.Extension F p 2

def basis : Module.Basis (Fin 2) F (Quadratic F p) :=
  Module.finBasisOfFinrankEq F (Quadratic F p) (FiniteField.finrank_extension F p 2)

def slEmbedding : NormOne F (Quadratic F p) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  slHom (basis F p)

theorem slEmbedding_injective : Function.Injective (slEmbedding F p) :=
  slHom_injective (basis F p)

theorem norm_one_card : Nat.card (NormOne F (Quadratic F p))=Nat.card F+1 := by
  let n := normUnits F (Quadratic F p)
  have hsurj : Function.Surjective n := FiniteField.unitsMap_norm_surjective F (Quadratic F p)
  have hm := n.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hsurj,Subgroup.card_top,
    Nat.card_units,Nat.card_units] at hm
  change Nat.card (NormOne F (Quadratic F p))*(Nat.card F-1)=
    Nat.card (Quadratic F p)-1 at hm
  rw [FiniteField.natCard_extension] at hm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hsub : Nat.card F-1+1=Nat.card F := Nat.sub_add_cancel (by omega)
  have he : (Nat.card F+1)*(Nat.card F-1)=(Nat.card F)^2-1 := by
    have hpow : 1 ≤ (Nat.card F)^2 := by nlinarith
    have hs := Nat.sub_add_cancel hpow
    nlinarith
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0<Nat.card F-1)
  exact hm.trans he.symm

theorem sl_range_card : Nat.card (slEmbedding F p).range=Nat.card F+1 := by
  exact (card_sl_range (basis F p)).trans (norm_one_card F p)

/-- The finite-field construction is sent into the original PSL2 quotient. -/
def projectiveEmbedding : NormOne F (Quadratic F p) →*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := projectiveHom (basis F p)

theorem projective_kernel_exact : (projectiveEmbedding F p).ker=
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).comap (slEmbedding F p) :=
  projective_kernel (basis F p)

end SymmetricSubgroupAsymptotics.FiniteFieldQuadraticNormOneEmbedding
