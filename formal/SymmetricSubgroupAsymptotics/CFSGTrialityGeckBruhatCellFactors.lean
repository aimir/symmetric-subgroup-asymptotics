import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelNegativeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
import Mathlib.Tactic.Group

/-! Actual Borel-times-inversion factors in a fixed Weyl cell are unique.
The inversion subgroup is the literal intersection inside the positive
group, and its conjugate lies in the same negative group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatCellFactors
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoGeckIntegralWord CFSGTrialityGeckBorelNegativeIntersection

theorem shifted_product_factors_injective {G C : Type*} [Group G] [Group C]
    (B V : Subgroup G) (W : G) (e : C →* G) (hei : Function.Injective e)
    (hdis : Disjoint B V) (hC : ∀ c, MulAut.conj W (e c) ∈ V) :
    Function.Injective (fun p : B × C => (p.1.val : G) * W * e p.2) := by
  rintro ⟨b, v⟩ ⟨b', v'⟩ he
  change b.val * W * e v = b'.val * W * e v' at he
  have hc : b'.val⁻¹ * b.val = MulAut.conj W (e (v' * v⁻¹)) := by
    change b'.val⁻¹ * b.val = W * e (v' * v⁻¹) * W⁻¹
    rw [map_mul, map_inv]
    calc
      _ = b'.val⁻¹ * (b.val * W * e v) * (e v)⁻¹ * W⁻¹ := by group
      _ = _ := by rw [he]; group
  have hb : b'.val⁻¹ * b.val = 1 := Subgroup.disjoint_def.mp hdis
    (B.mul_mem (B.inv_mem b'.property) b.property) (hc ▸ hC (v' * v⁻¹))
  have hbb : b = b' := Subtype.ext (inv_mul_eq_one.mp hb).symm
  have hvv : v = v' := by
    apply hei
    rw [hbb] at he
    exact mul_left_cancel he
  exact Prod.ext hbb hvv

abbrev InversionPart (K : Type) [Field K] (w : List (Fin 4)) :=
  wordSignPart (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K w true

def inversionEmbedding (K : Type) [Field K] (w : List (Fin 4)) :
    InversionPart K w →* (Matrix GeckIndex GeckIndex K)ˣ :=
  (PositiveGroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K).subtype.comp
      (InversionPart K w).subtype

theorem inversionEmbedding_injective (K : Type) [Field K] (w : List (Fin 4)) :
    Function.Injective (inversionEmbedding K w) := by
  intro v u he
  exact Subtype.ext (Subtype.ext he)

theorem borel_inversion_factors_injective (K : Type) [Field K] (w : List (Fin 4)) :
    Function.Injective (fun p :
      borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K × InversionPart K w =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ) *
        wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K w * inversionEmbedding K w p.2) := by
  apply shifted_product_factors_injective _
    (rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K true) _ _
    (inversionEmbedding_injective K w) (borel_negative_disjoint K)
  intro v
  rw [word_eq_canonicalWord]
  exact v.property

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatCellFactors
