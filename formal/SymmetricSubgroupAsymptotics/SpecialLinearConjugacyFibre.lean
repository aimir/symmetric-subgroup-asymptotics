import SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyFibre
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The literal GL-to-SL class splitting in every dimension is bounded
by gcd(q-1,n). Scalar matrices centralize every matrix, and their actual
determinants form the subgroup of nth powers of the finite field's units.
No conjugacy normal form or classification assumption is used.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre

variable (K I : Type*) [Field K] [Fintype I] [DecidableEq I] [Nonempty I]

abbrev specialLinearKernel : Subgroup (Matrix.GeneralLinearGroup I K) :=
  (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup I K →* Kˣ).ker

def specialLinearKernelEquiv : Matrix.SpecialLinearGroup I K ≃* specialLinearKernel K I where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A,Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun g := ⟨(g.val : Matrix I I K),by
    have h := congrArg (fun u:Kˣ=>(u:K)) g.property
    exact h⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul Matrix.SpecialLinearGroup.toGL A B

theorem specialLinearKernelEquiv_val (A:Matrix.SpecialLinearGroup I K) :
    (specialLinearKernelEquiv K I A).val=Matrix.SpecialLinearGroup.toGL A := rfl

theorem determinant_surjective : Function.Surjective
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup I K →* Kˣ) := by
  classical
  intro u
  let i:I := Classical.choice inferInstance
  let M:Matrix I I K := Matrix.diagonal (fun j=>if j=i then (u:K) else 1)
  have hdet : M.det=(u:K) := by simp [M,Matrix.det_diagonal]
  let P := Matrix.GeneralLinearGroup.mkOfDetNeZero M (hdet ▸ u.ne_zero)
  refine ⟨P,?_⟩
  apply Units.ext
  exact hdet

theorem scalar_mem_centralizer (u:Kˣ) (x:Matrix.GeneralLinearGroup I K) :
    Matrix.GeneralLinearGroup.scalar I u ∈ Subgroup.centralizer ({x}:Set _) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  have he:y=x := Set.mem_singleton_iff.mp hy
  subst y
  apply Units.ext
  change (x:Matrix I I K)*Matrix.scalar I (u:K)=Matrix.scalar I (u:K)*(x:Matrix I I K)
  exact (Matrix.scalar_commute (u:K) (fun a=>Commute.all _ a) (x:Matrix I I K)).eq.symm

theorem join_centralizer_index_le_gcd [Finite K] (x:specialLinearKernel K I) :
    (specialLinearKernel K I ⊔
      Subgroup.centralizer ({(x:Matrix.GeneralLinearGroup I K)}:Set _)).index ≤
      (Nat.card K-1).gcd (Fintype.card I) := by
  letI : Fintype K := Fintype.ofFinite K
  let D : Matrix.GeneralLinearGroup I K →* Kˣ := Matrix.GeneralLinearGroup.det
  let J := specialLinearKernel K I ⊔
    Subgroup.centralizer ({(x:Matrix.GeneralLinearGroup I K)}:Set _)
  have hpow : (powMonoidHom (Fintype.card I):Kˣ→*Kˣ).range ≤ J.map D := by
    rintro z ⟨u,rfl⟩
    refine ⟨Matrix.GeneralLinearGroup.scalar I u,?_,?_⟩
    · exact (show Subgroup.centralizer ({x.val}:Set _)≤J from le_sup_right)
        (scalar_mem_centralizer K I u x.val)
    · exact Matrix.GeneralLinearGroup.det_scalar (n:=I) u
  have hidx : (J.map D).index=J.index :=
    Subgroup.index_map_eq (H:=J) (determinant_surjective K I) le_sup_left
  calc
    J.index=(J.map D).index := hidx.symm
    _ ≤ (powMonoidHom (Fintype.card I):Kˣ→*Kˣ).range.index :=
      Subgroup.index_antitone hpow
    _ = (Nat.card K-1).gcd (Fintype.card I) := by
      rw [IsCyclic.index_powMonoidHom_range,Nat.card_units]

theorem class_fibre_card_le_gcd [Finite K] (A:Matrix.SpecialLinearGroup I K) :
    Nat.card {c:ConjClasses (Matrix.SpecialLinearGroup I K) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} ≤
      (Nat.card K-1).gcd (Fintype.card I) := by
  letI : Finite (Matrix.SpecialLinearGroup I K) :=
    Finite.of_injective (fun g:Matrix.SpecialLinearGroup I K=>g.val) Subtype.val_injective
  letI : Finite (ConjClasses (specialLinearKernel K I)) :=
    Finite.of_surjective (@ConjClasses.mk (specialLinearKernel K I) _) ConjClasses.mk_surjective
  let E := specialLinearKernelEquiv K I
  let embed :
      {c:ConjClasses (Matrix.SpecialLinearGroup I K) //
        ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} →
      {c:ConjClasses (specialLinearKernel K I) //
        ConjClasses.map (specialLinearKernel K I).subtype c=ConjClasses.mk (E A).val} :=
    fun c=>⟨ConjClasses.map E.toMonoidHom c.val,by
      obtain ⟨g,hg⟩ := ConjClasses.mk_surjective c.val
      have hc := c.property
      rw [←hg] at hc ⊢
      change ConjClasses.mk (specialLinearKernelEquiv K I g).val=
        ConjClasses.mk (specialLinearKernelEquiv K I A).val
      rw [specialLinearKernelEquiv_val,specialLinearKernelEquiv_val]
      exact hc⟩
  have hinj : Function.Injective embed := by
    intro c d he
    apply Subtype.ext
    have hh := congrArg (fun z=>ConjClasses.map E.symm.toMonoidHom z.val) he
    obtain ⟨g,hg⟩ := ConjClasses.mk_surjective c.val
    obtain ⟨h,hh'⟩ := ConjClasses.mk_surjective d.val
    change ConjClasses.map E.symm.toMonoidHom (ConjClasses.map E.toMonoidHom c.val)=
      ConjClasses.map E.symm.toMonoidHom (ConjClasses.map E.toMonoidHom d.val) at hh
    rw [←hg,←hh'] at hh ⊢
    change ConjClasses.mk (E.symm (E g))=ConjClasses.mk (E.symm (E h)) at hh
    simpa only [E.symm_apply_apply] using hh
  exact (Nat.card_le_card_of_injective embed hinj).trans
    ((NormalSubgroupConjugacyFibre.fibre_card_le_join_centralizer_index
      (specialLinearKernel K I) (E A)).trans (join_centralizer_index_le_gcd K I (E A)))

theorem class_fibre_card_le_card_index [Finite K] (A:Matrix.SpecialLinearGroup I K) :
    Nat.card {c:ConjClasses (Matrix.SpecialLinearGroup I K) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} ≤ Fintype.card I :=
  (class_fibre_card_le_gcd K I A).trans (Nat.gcd_le_right _ Fintype.card_pos)

end SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre
