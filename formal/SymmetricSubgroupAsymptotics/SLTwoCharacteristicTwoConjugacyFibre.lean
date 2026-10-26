import SymmetricSubgroupAsymptotics.SLTwoConjugacyFibre
import Mathlib.FieldTheory.Finite.Basic

/-! In a finite characteristic-two field every nonzero determinant is a
square. Actual scalar GL2 matrices therefore fill every determinant class
inside the centralizer; an original GL2 class cannot split into multiple
SL2 classes. No conjugacy-class table or torus identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoConjugacyFibre
open SLTwoConjugacyFibre
variable (K : Type*) [Field K]

/-- The literal square map on actual field units is surjective. -/
theorem squares_range_eq_top [Finite K] (hchar : ringChar K=2) :
    (powMonoidHom 2 : Kˣ→*Kˣ).range=⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,ha⟩ := FiniteField.isSquare_of_char_two hchar (z:K)
  have ha0 : a≠0 := by
    intro hz
    exact Units.ne_zero z (by simpa only [hz,zero_mul] using ha)
  refine ⟨Units.mk0 a ha0,?_⟩
  apply Units.ext
  change a^2=(z:K)
  simpa only [pow_two] using ha.symm

/-- All determinant cosets occur in the actual centralizer join. -/
theorem join_centralizer_index_eq_one [Finite K] (hchar : ringChar K=2)
    (x : specialLinearKernel K) :
    (specialLinearKernel K ⊔ Subgroup.centralizer
      ({(x:Matrix.GeneralLinearGroup (Fin 2) K)} : Set _)).index=1 := by
  let D : Matrix.GeneralLinearGroup (Fin 2) K→*Kˣ := Matrix.GeneralLinearGroup.det
  let J := specialLinearKernel K ⊔
    Subgroup.centralizer ({(x:Matrix.GeneralLinearGroup (Fin 2) K)} : Set _)
  have hsq : (powMonoidHom 2 : Kˣ→*Kˣ).range≤J.map D := by
    rintro z ⟨u,rfl⟩
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u,?_,?_⟩
    · exact (show Subgroup.centralizer ({x.val} : Set _)≤J from le_sup_right)
        (scalar_mem_centralizer K u x.val)
    · change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u)=u^2
      simpa only [Fintype.card_fin] using
        (Matrix.GeneralLinearGroup.det_scalar (n:=Fin 2) u)
  have htop : J.map D=⊤ := by
    apply top_unique
    rw [←squares_range_eq_top K hchar]
    exact hsq
  have hidx : (J.map D).index=J.index :=
    Subgroup.index_map_eq (H:=J) (determinant_surjective K) le_sup_left
  exact hidx.symm.trans (Subgroup.index_eq_one.mpr htop)

theorem class_fibre_card_le_one [Finite K] (hchar : ringChar K=2) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 2) K) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)}≤1 := by
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
      (specialLinearKernel K) (E A)).trans_eq (join_centralizer_index_eq_one K hchar (E A)))

end SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoConjugacyFibre
