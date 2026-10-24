import SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyFibre
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Each actual GL2 conjugacy class contains at most two SL2 classes.
The determinant kernel is identified with the literal special linear
group. Scalar GL2 units centralize every matrix, and their determinants
are precisely squares, so the centralizer join has index at most two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLTwoConjugacyFibre
variable (K : Type*) [Field K]

abbrev specialLinearKernel : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker

def specialLinearKernelEquiv : Matrix.SpecialLinearGroup (Fin 2) K ≃* specialLinearKernel K where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun g := ⟨(g.val : Matrix (Fin 2) (Fin 2) K), by
    have h := congrArg (fun u : Kˣ => (u : K)) g.property
    exact h⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul Matrix.SpecialLinearGroup.toGL A B

theorem specialLinearKernelEquiv_val (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (specialLinearKernelEquiv K A).val=Matrix.SpecialLinearGroup.toGL A := rfl

theorem determinant_surjective : Function.Surjective
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ) := by
  intro u
  let P := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(u:K),0;0,1] : Matrix (Fin 2) (Fin 2) K)
    (by simpa only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] using u.ne_zero)
  refine ⟨P, ?_⟩
  apply Units.ext
  change Matrix.det (!![(u:K),0;0,1] : Matrix (Fin 2) (Fin 2) K)=(u:K)
  simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]

theorem scalar_mem_centralizer (u : Kˣ) (x : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.centralizer ({x} : Set _) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  have he : y=x := Set.mem_singleton_iff.mp hy
  subst y
  apply Units.ext
  change (x : Matrix (Fin 2) (Fin 2) K)*Matrix.scalar (Fin 2) (u:K)=
    Matrix.scalar (Fin 2) (u:K)*(x : Matrix (Fin 2) (Fin 2) K)
  exact (Matrix.scalar_commute (u:K) (fun a => Commute.all _ a)
    (x : Matrix (Fin 2) (Fin 2) K)).eq.symm

theorem join_centralizer_index_le_two [Finite K] (x : specialLinearKernel K) :
    (specialLinearKernel K ⊔ Subgroup.centralizer ({(x : Matrix.GeneralLinearGroup (Fin 2) K)} : Set _)).index≤2 := by
  let D : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ := Matrix.GeneralLinearGroup.det
  let J := specialLinearKernel K ⊔
    Subgroup.centralizer ({(x : Matrix.GeneralLinearGroup (Fin 2) K)} : Set _)
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range≤J.map D := by
    rintro z ⟨u,rfl⟩
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u, ?_, ?_⟩
    · exact (show Subgroup.centralizer ({x.val} : Set _)≤J from le_sup_right)
        (scalar_mem_centralizer K u x.val)
    · change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u)=u^2
      simpa only [Fintype.card_fin] using
        (Matrix.GeneralLinearGroup.det_scalar (n:=Fin 2) u)
  have hidx : (J.map D).index=J.index :=
    Subgroup.index_map_eq (H:=J) (determinant_surjective K) le_sup_left
  calc
    J.index=(J.map D).index := hidx.symm
    _ ≤(powMonoidHom 2 : Kˣ →* Kˣ).range.index := Subgroup.index_antitone hsq
    _ ≤2 := CFSGFiniteFieldSquareIndex.squares_index_le_two K

theorem class_fibre_card_le_two [Finite K] (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 2) K) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)}≤2 := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Finite.of_injective (fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.val) Subtype.val_injective
  letI : Finite (ConjClasses (specialLinearKernel K)) :=
    Finite.of_surjective (@ConjClasses.mk (specialLinearKernel K) _) ConjClasses.mk_surjective
  let E := specialLinearKernelEquiv K
  let embed :
      {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 2) K) //
        ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} →
      {c : ConjClasses (specialLinearKernel K) //
        ConjClasses.map (specialLinearKernel K).subtype c=
          ConjClasses.mk (E A).val} := fun c =>
    ⟨ConjClasses.map E.toMonoidHom c.val, by
      obtain ⟨g,hg⟩ := ConjClasses.mk_surjective c.val
      have hc := c.property
      rw [← hg] at hc ⊢
      change ConjClasses.mk (specialLinearKernelEquiv K g).val=
        ConjClasses.mk (specialLinearKernelEquiv K A).val
      rw [specialLinearKernelEquiv_val, specialLinearKernelEquiv_val]
      exact hc⟩
  have hinj : Function.Injective embed := by
    intro c d he
    apply Subtype.ext
    have hh := congrArg (fun z => ConjClasses.map E.symm.toMonoidHom z.val) he
    obtain ⟨g,hg⟩ := ConjClasses.mk_surjective c.val
    obtain ⟨h,hh'⟩ := ConjClasses.mk_surjective d.val
    change ConjClasses.map E.symm.toMonoidHom (ConjClasses.map E.toMonoidHom c.val)=
      ConjClasses.map E.symm.toMonoidHom (ConjClasses.map E.toMonoidHom d.val) at hh
    rw [←hg, ←hh'] at hh ⊢
    change ConjClasses.mk (E.symm (E g))=ConjClasses.mk (E.symm (E h)) at hh
    simpa only [E.symm_apply_apply] using hh
  exact (Nat.card_le_card_of_injective embed hinj).trans
    ((NormalSubgroupConjugacyFibre.fibre_card_le_join_centralizer_index
      (specialLinearKernel K) (E A)).trans (join_centralizer_index_le_two K (E A)))

end SymmetricSubgroupAsymptotics.SLTwoConjugacyFibre
