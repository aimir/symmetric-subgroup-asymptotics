import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularCenter
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Exact transport of the original unitriangular group and its centre
through the original SL centre quotient. The map is injective because
its matrices have diagonal one; a central scalar has no residual freedom. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperCenter
open Matrix CFSGUpperUnitriangular CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F] {n : ℕ}

abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) F

def projection : SL F n→*PSL (F:=F) (n:=n) :=
  QuotientGroup.mk' (Subgroup.center (SL F n))

def upperHom : upperUnitriangular F n→*PSL (F:=F) (n:=n) :=
  (projection (F:=F) (n:=n)).comp (upperUnitriangular F n).subtype

theorem upperHom_injective (hn : 1≤n) : Function.Injective (upperHom (F:=F) (n:=n)) := by
  apply (MonoidHom.ker_eq_bot_iff (upperHom (F:=F) (n:=n))).mp
  apply bot_unique
  intro A hA
  have hc : A.val∈Subgroup.center (SL F n) := (QuotientGroup.eq_one_iff _).mp hA
  let i : Fin n := ⟨0,by omega⟩
  have he := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc i
  rw [A.property.2 i] at he
  apply (Subgroup.mem_bot).mpr
  apply Subtype.ext
  apply Subtype.ext
  exact he.symm.trans (map_one (Matrix.scalar (Fin n)))

def projectiveUpper : Subgroup (PSL (F:=F) (n:=n)) :=
  (upperHom (F:=F) (n:=n)).range

def upperEquiv (hn : 1≤n) : upperUnitriangular F n≃*projectiveUpper (F:=F) (n:=n) :=
  MonoidHom.ofInjective (upperHom_injective hn)

/-- Every central element of the actual projective U is represented by
one original highest-root matrix. No quotient-centre enlargement occurs. -/
theorem center_projectiveUpper_highestRoot (hn : 2≤n)
    (g : projectiveUpper (F:=F) (n:=n))
    (hg : g∈Subgroup.center (projectiveUpper (F:=F) (n:=n))) :
    ∃a : F,(g : PSL (F:=F) (n:=n))=
      projection (elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
        intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a) := by
  let e := upperEquiv (F:=F) (n:=n) (by omega : 1≤n)
  let A := e.symm g
  have hA : A∈Subgroup.center (upperUnitriangular F n) := by
    apply Subgroup.mem_center_iff.mpr
    intro B
    apply e.injective
    rw [map_mul,map_mul]
    have he : e A=g := e.apply_symm_apply g
    rw [he]
    exact Subgroup.mem_center_iff.mp hg (e B)
  obtain ⟨a,ha⟩ := center_upperUnitriangular_eq_highestRoot hn A hA
  refine ⟨a,?_⟩
  have he := congrArg (fun t : projectiveUpper (F:=F) (n:=n) => t.val) (e.apply_symm_apply g)
  change upperHom A=(g : PSL (F:=F) (n:=n)) at he
  rw [←he]
  change projection A.val=_
  rw [ha]

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperCenter
