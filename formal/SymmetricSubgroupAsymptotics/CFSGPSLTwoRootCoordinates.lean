import SymmetricSubgroupAsymptotics.CFSGPSLTwoGoodSylow

/-! Literal root coordinates in the original PSL2 central quotient. The
upper root map remains injective, and the actual determinant-one torus
acts by square scalars. No isomorphic permutation model is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
variable {F : Type*} [Field F]

abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

def projection : SL2 (F:=F)→*PSL (F:=F) :=
  QuotientGroup.mk' (Subgroup.center (SL2 (F:=F)))

theorem projection_surjective : Function.Surjective (projection (F:=F)) :=
  QuotientGroup.mk'_surjective _

def projectiveUpper (a : F) : PSL (F:=F) := projection (upper a)

def projectiveUpperHom : Multiplicative F→*PSL (F:=F) :=
  (projection (F:=F)).comp (CFSGSLTwoUpperRoots.upperHom (F:=F))

theorem projectiveUpperHom_injective : Function.Injective (projectiveUpperHom (F:=F)) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveUpperHom (F:=F))).mp
  apply bot_unique
  intro a ha
  apply (Subgroup.mem_bot).mpr
  have hc : upper a.toAdd∈Subgroup.center (SL2 (F:=F)) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc (0 : Fin 2)
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hs
  have hl : Matrix.scalar (Fin 2) ((upper a.toAdd).val 0 0) 0 1=0 := by
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2)≠1)]
  dsimp only at he
  rw [hl,upper_entry01] at he
  exact congrArg Multiplicative.ofAdd he.symm

def projectiveRoot : Subgroup (PSL (F:=F)) := (projectiveUpperHom (F:=F)).range

def projectiveRootEquiv : Multiplicative F ≃* projectiveRoot (F:=F) :=
  MonoidHom.ofInjective (projectiveUpperHom_injective (F:=F))

theorem projectiveUpper_mem (a : F) : projectiveUpper a∈projectiveRoot (F:=F) :=
  ⟨Multiplicative.ofAdd a,rfl⟩

@[simp] theorem projectiveUpperHom_apply (a : Multiplicative F) :
    projectiveUpperHom a=projectiveUpper a.toAdd := rfl

@[simp] theorem projectiveUpper_zero : projectiveUpper (0 : F)=1 :=
  map_one (projectiveUpperHom (F:=F))

theorem projectiveUpper_add (a b : F) :
    projectiveUpper (a+b)=projectiveUpper a*projectiveUpper b :=
  map_mul (projectiveUpperHom (F:=F)) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

theorem projectiveUpper_injective : Function.Injective (projectiveUpper (F:=F)) := by
  intro a b h
  exact congrArg Multiplicative.toAdd (projectiveUpperHom_injective (F:=F) h)

def projectiveTorus (c : Fˣ) : PSL (F:=F) :=
  projection (torus (by decide : (0 : Fin 2)≠1) c)

def projectiveWeyl : PSL (F:=F) := projection (weyl (F:=F))

theorem projective_torus_conjugation (c : Fˣ) (a : F) :
    projectiveTorus c*projectiveUpper a*(projectiveTorus c)⁻¹=
      projectiveUpper ((c : F)^2*a) := by
  change projection (torus (by decide : (0 : Fin 2)≠1) c)*projection (upper a)*
    (projection (torus (by decide : (0 : Fin 2)≠1) c))⁻¹=_
  rw [←map_inv,←map_mul,←map_mul]
  change projection (torus (by decide : (0 : Fin 2)≠1) c*
    CFSGTypeAElementaryMatrices.elementary (by decide : (0 : Fin 2)≠1) a*
      (torus (by decide : (0 : Fin 2)≠1) c)⁻¹)=_
  rw [torus_conjugation]
  rfl

theorem projective_weyl_upper (a : F) :
    projectiveWeyl*projectiveUpper a*(projectiveWeyl (F:=F))⁻¹=projection (lower (-a)) := by
  change projection (weyl (F:=F))*projection (upper a)*(projection (weyl (F:=F)))⁻¹=_
  rw [←map_inv,←map_mul,←map_mul,weyl_upper]

theorem sl_weyl_coe : (weyl (F:=F)).val=!![0,1;-1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,upper,lower,CFSGTypeAElementaryMatrices.elementary,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.transvection,
      Matrix.single_apply,Matrix.one_apply]

theorem projectiveWeyl_square : projectiveWeyl (F:=F)*projectiveWeyl=1 := by
  rw [projectiveWeyl,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(-1 : F),?_,?_⟩
  · simp only [Fintype.card_fin]
    ring
  · change Matrix.scalar (Fin 2) (-1 : F)=(weyl (F:=F)).val*(weyl (F:=F)).val
    rw [sl_weyl_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar_apply]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
