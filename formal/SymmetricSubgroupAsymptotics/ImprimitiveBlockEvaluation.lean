import SymmetricSubgroupAsymptotics.ChiefBlockKernel
import Mathlib.GroupTheory.GroupAction.Hom

/-! Actual local coordinates from an original equivariant block map.
The component is the literal stabilizer image on the original fibre.
Faithfulness and transitivity prove that its original conjugate
evaluations separate every subgroup of the original block kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω) (x₀:X)

abbrev originalBlockFibre := {ω:Ω // b ω=x₀}

def originalBlockFibreAction : MulAction.stabilizer A x₀→*Equiv.Perm (originalBlockFibre b x₀) where
  toFun h := {
    toFun ω := ⟨(h:A)•ω.1,by
      rw [hb,ω.2]
      exact h.2⟩
    invFun ω := ⟨(h:A)⁻¹•ω.1,by
      rw [hb,ω.2]
      exact (h⁻¹).2⟩
    left_inv ω := Subtype.ext (inv_smul_smul (h:A) ω.1)
    right_inv ω := Subtype.ext (smul_inv_smul (h:A) ω.1) }
  map_one' := by
    apply Equiv.ext
    intro ω
    apply Subtype.ext
    exact one_smul A ω.1
  map_mul' h k := by
    apply Equiv.ext
    intro ω
    apply Subtype.ext
    exact mul_smul (h:A) (k:A) ω.1

def originalBlockComponent : Subgroup (Equiv.Perm (originalBlockFibre b x₀)) :=
  (originalBlockFibreAction b hb x₀).range

def blockKernelToStabilizer (N : Subgroup A)
    (hN : N≤(MulAction.toPermHom A X).ker) : N→*MulAction.stabilizer A x₀ where
  toFun n := ⟨(n:A),by
    have h := congrArg (fun σ : Equiv.Perm X=>σ x₀) (hN n.2)
    exact h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def originalBlockEvaluation (N : Subgroup A)
    (hN : N≤(MulAction.toPermHom A X).ker) : N→* originalBlockComponent b hb x₀ :=
  (originalBlockFibreAction b hb x₀).rangeRestrict.comp (blockKernelToStabilizer x₀ N hN)

theorem originalBlockEvaluation_apply (N : Subgroup A)
    (hN : N≤(MulAction.toPermHom A X).ker) (n:N) (ω:originalBlockFibre b x₀) :
    (((originalBlockEvaluation b hb x₀ N hN n:
      Equiv.Perm (originalBlockFibre b x₀)) ω):Ω)=(n:A)•ω.1 := rfl

/-- The all-conjugate local kernel is trivial on the original faithful
action. This supplies the bottom of the actual local-chief chain. -/
theorem originalBlockEvaluation_conjugates_separate
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal] (hN : N≤(MulAction.toPermHom A X).ker)
    (n:N) (hn : ∀a:A,originalBlockEvaluation b hb x₀ N hN (MulAut.conjNormal a n)=1) :
    n=1 := by
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α:=Ω)
  intro ω
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A x₀ (b ω)
  let v : originalBlockFibre b x₀ := ⟨a⁻¹•ω,by rw [hb,←ha,inv_smul_smul]⟩
  have h := congrArg (fun r : originalBlockComponent b hb x₀=>
    ((r:Equiv.Perm (originalBlockFibre b x₀)) v:Ω)) (hn a⁻¹)
  change (MulAut.conjNormal a⁻¹ n:A)•(a⁻¹•ω)=a⁻¹•ω at h
  rw [MulAut.conjNormal_apply,inv_inv] at h
  have hh := congrArg (fun z:Ω=>a•z) h
  simpa only [mul_smul,smul_inv_smul,inv_smul_smul,OneMemClass.coe_one,one_smul] using hh

end SymmetricSubgroupAsymptotics
