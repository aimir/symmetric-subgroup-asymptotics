import SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators
import SymmetricSubgroupAsymptotics.OddKernelCyclicUpperRelativeHead
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuarterTurnSixActualUpper
open SemidirectProduct
open SixPointTernaryQuarterTurnNormalGenerators (Model Upper gen literalAction)

theorem action_injective : Function.Injective literalAction := by
  have h : ∀ (v w : Fin 2 → ZMod 3) (c d : Upper),
      (∀ i : Fin 6,literalAction ⟨Multiplicative.ofAdd v,c⟩ i=
        literalAction ⟨Multiplicative.ofAdd w,d⟩ i) →
      v 0=w 0 ∧ v 1=w 1 ∧ c=d := by decide +kernel
  rintro ⟨v,c⟩ ⟨w,d⟩ he
  have hh := h v.toAdd w.toAdd c d
    (fun i => congrArg (fun p : Equiv.Perm (Fin 6) => p i) he)
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hh.1
    · exact hh.2.1
  · exact hh.2.2
def canonicalEquiv : Model ≃* literalAction.range :=
  MulEquiv.ofBijective literalAction.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),literalAction.rangeRestrict_surjective⟩

variable (P : Subgroup (Equiv.Perm (Fin 6))) (hle : P≤literalAction.range)
def toModel : P →* Model :=
  canonicalEquiv.symm.toMonoidHom.comp (Subgroup.inclusion hle)
theorem toModel_action (p : P) : literalAction (toModel P hle p)=(p : Equiv.Perm (Fin 6)) :=
  congrArg Subtype.val (canonicalEquiv.apply_symm_apply ⟨p.val,hle p.property⟩)
theorem toModel_injective : Function.Injective (toModel P hle) := by
  intro p q h
  apply Subtype.ext
  simpa only [toModel_action] using congrArg literalAction h

def projection : P →* Upper := (rightHom : Model →* Upper).comp (toModel P hle)
theorem projection_code (p : P) (g : Model) (he : literalAction g=(p : Equiv.Perm (Fin 6))) :
    projection P hle p=g.right := by
  have ht : toModel P hle p=g := action_injective ((toModel_action P hle p).trans he.symm)
  change (toModel P hle p).right=g.right
  rw [ht]

theorem projection_surjective (p : P) (g : Model)
    (he : literalAction g=(p : Equiv.Perm (Fin 6))) (hg : g.right=gen) :
    Function.Surjective (projection P hle) := by
  intro c
  refine ⟨p^c.toAdd.val,?_⟩
  rw [map_pow,projection_code P hle p g he,hg]
  revert c
  decide +kernel

theorem kernel_isPGroup : IsPGroup 3 (projection P hle).ker := by
  have hc : ∀ g : Model,g.right=1 → g^3=1 := by
    rintro ⟨v,c⟩ hc
    change c=1 at hc
    subst c
    change (inl v : Model)^3=1
    have hv : v^3=1 := by
      apply Multiplicative.toAdd.injective
      funext i
      change 3 • v.toAdd i=0
      exact ZModModule.char_nsmul_eq_zero 3 _
    rw [← map_pow,hv,map_one]
  intro x
  refine ⟨1,?_⟩
  apply Subtype.ext
  apply toModel_injective P hle
  change toModel P hle ((x.val)^3)=toModel P hle 1
  rw [map_pow,map_one]
  apply hc
  exact x.property

include hle in
theorem isSolvable (p : P) (g : Model)
    (he : literalAction g=(p : Equiv.Perm (Fin 6))) (hg : g.right=gen) : IsSolvable P := by
  let beta := projection P hle
  letI : Group.IsNilpotent beta.ker := (kernel_isPGroup P hle).isNilpotent
  exact solvable_of_ker_le_range beta.ker.subtype beta (by rw [Subgroup.range_subtype])
end SymmetricSubgroupAsymptotics.QuarterTurnSixActualUpper
