import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Exact actual PSL2 torus and group cardinalities in odd
characteristic. The scalar negative identity supplies the second
kernel element; the checked square-one kernel bound supplies the upper
bound. No centre-size formula or small-field group identification is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoOddTorusCardinality
open Matrix CFSGTypeARootTorus CFSGSLTwoBruhat
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry
variable {F : Type} [Field F]

theorem minusOne_mem_torus_kernel : (-1 : Fˣ)∈(projectiveTorusHom (F:=F)).ker := by
  change projection (torusHom (-1 : Fˣ))=1
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(-1 : F),?_,?_⟩
  · simp only [Fintype.card_fin]
    ring
  · change Matrix.scalar (Fin 2) (-1 : F)=
      (torus (by decide : (0 : Fin 2)≠1) (-1 : Fˣ)).val
    rw [torus_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem torus_kernel_card_eq_two [Finite F] (hchar : ringChar F≠2) :
    Nat.card (projectiveTorusHom (F:=F)).ker=2 := by
  have hne : (projectiveTorusHom (F:=F)).ker≠⊥ := by
    intro he
    have hm := minusOne_mem_torus_kernel (F:=F)
    rw [he] at hm
    have hu : (-1 : Fˣ)=1 := Subgroup.mem_bot.mp hm
    have hv : (-1 : F)=1 := congrArg (fun u : Fˣ => (u:F)) hu
    exact Ring.neg_one_ne_one_of_char_ne_two hchar hv
  have hp := Nat.card_pos (α:=(projectiveTorusHom (F:=F)).ker)
  have hn : Nat.card (projectiveTorusHom (F:=F)).ker≠1 :=
    fun h => hne (Subgroup.card_eq_one.mp h)
  have hb := torus_kernel_card_le_two (F:=F)
  omega

theorem twice_pairTorus_card_eq_units [Finite F] (hchar : ringChar F≠2) :
    2*Nat.card (pairTorus (F:=F))=Nat.card Fˣ := by
  have hc := (projectiveTorusHom (F:=F)).ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  change Nat.card (projectiveTorusHom (F:=F)).ker*Nat.card (pairTorus (F:=F))=
    Nat.card Fˣ at hc
  rw [torus_kernel_card_eq_two hchar] at hc
  exact hc

theorem twice_projective_card_eq [Finite F] (hchar : ringChar F≠2) :
    2*Nat.card (PSL (F:=F))=(Nat.card F-1)*Nat.card F*(Nat.card F+1) := by
  rw [projective_card_eq_torus_mul]
  calc
    2*(Nat.card (pairTorus (F:=F))*Nat.card F*(Nat.card F+1))=
        (2*Nat.card (pairTorus (F:=F)))*Nat.card F*(Nat.card F+1) := by ring
    _ =_ := by rw [twice_pairTorus_card_eq_units hchar,Nat.card_units]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoOddTorusCardinality
