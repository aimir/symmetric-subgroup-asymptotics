import SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry

/-! The actual projective diagonal torus loses at most the two scalar
square roots of one. This includes characteristic two and the fields of
orders four and five without exceptional isomorphism assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
open CFSGPSLTwoRootCoordinates CFSGSLTwoBruhat
variable {F : Type*} [Field F]

theorem torus_kernel_square_one (c : Fˣ)
    (hc : c∈(projectiveTorusHom (F:=F)).ker) : (c : F)^2=1 := by
  have hz : torusHom c∈Subgroup.center (SL2 (F:=F)) := (QuotientGroup.eq_one_iff _).mp hc
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hs
  change Matrix.scalar (Fin 2) ((torusHom c).val 0 0) 1 1=(torusHom c).val 1 1 at he
  change Matrix.scalar (Fin 2)
    ((torus (by decide : (0 : Fin 2)≠1) c).val 0 0) 1 1=
      (torus (by decide : (0 : Fin 2)≠1) c).val 1 1 at he
  rw [torus_coe] at he
  simp only [Matrix.scalar_apply,Matrix.diagonal_apply_eq] at he
  simp at he
  calc
    (c : F)^2=(c : F)*(c : F) := pow_two _
    _ = (c : F)*(c : F)⁻¹ := congrArg (fun x : F => (c : F)*x) he
    _ = 1 := mul_inv_cancel₀ (Units.ne_zero c)

theorem torus_kernel_card_le_two : Nat.card (projectiveTorusHom (F:=F)).ker≤2 := by
  let code : (projectiveTorusHom (F:=F)).ker → Bool := fun c => decide ((c.val : F)=1)
  have hi : Function.Injective code := by
    intro c d he
    have hc := torus_kernel_square_one c.val c.property
    have hd := torus_kernel_square_one d.val d.property
    change decide ((c.val : F)=1)=decide ((d.val : F)=1) at he
    have hiff : ((c.val : F)=1 ↔ (d.val : F)=1) := decide_eq_decide.mp he
    by_cases hc1 : (c.val : F)=1
    · have hd1 : (d.val : F)=1 := hiff.mp hc1
      exact Subtype.ext (Units.ext (hc1.trans hd1.symm))
    · have hd1 : (d.val : F)≠1 := fun hn => hc1 (hiff.mpr hn)
      have hcneg : (c.val : F)= -1 := (sq_eq_one_iff.mp hc).resolve_left hc1
      have hdneg : (d.val : F)= -1 := (sq_eq_one_iff.mp hd).resolve_left hd1
      exact Subtype.ext (Units.ext (hcneg.trans hdneg.symm))
  simpa using Nat.card_le_card_of_injective code hi

theorem card_units_le_two_mul_pairTorus [Finite F] :
    Nat.card Fˣ≤2*Nat.card (pairTorus (F:=F)) := by
  have hc := (projectiveTorusHom (F:=F)).ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  change Nat.card (projectiveTorusHom (F:=F)).ker*Nat.card (pairTorus (F:=F))=
    Nat.card Fˣ at hc
  rw [←hc]
  exact Nat.mul_le_mul_right _ torus_kernel_card_le_two

theorem field_card_sub_one_le_twice_pairTorus [Finite F] :
    Nat.card F-1≤2*Nat.card (pairTorus (F:=F)) := by
  rw [←Nat.card_units]
  exact card_units_le_two_mul_pairTorus

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
