import SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre
import Mathlib.Tactic.Group

/-! A literal determinant-surjective centralizer gives one SL class
inside its actual GL class. The same witness property transports through
actual GL conjugators. This is structural input for the existing normal
forms, not a supplied class capacity or a conjugacy classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SpecialLinearCentralizerDeterminantFibre
open SpecialLinearConjugacyFibre

variable (K I : Type*) [Field K] [Fintype I] [DecidableEq I] [Nonempty I]

private theorem join_centralizer_index_eq_one [Finite K] (x : specialLinearKernel K I)
    (hdet : ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup I K,
      Commute x.val P ∧ Matrix.GeneralLinearGroup.det P=u) :
    (specialLinearKernel K I ⊔ Subgroup.centralizer ({x.val} : Set _)).index=1 := by
  let D : Matrix.GeneralLinearGroup I K →* Kˣ := Matrix.GeneralLinearGroup.det
  let J := specialLinearKernel K I ⊔ Subgroup.centralizer ({x.val} : Set _)
  have htop : J.map D=⊤ := by
    apply top_unique
    intro u _
    obtain ⟨P,hP,hD⟩ := hdet u
    have hcent : P ∈ Subgroup.centralizer ({x.val} : Set _) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have he : y=x.val := Set.mem_singleton_iff.mp hy
      subst y
      exact hP.eq
    exact ⟨P,(show Subgroup.centralizer ({x.val} : Set _) ≤ J from le_sup_right) hcent,hD⟩
  have hidx : (J.map D).index=J.index :=
    Subgroup.index_map_eq (H := J) (determinant_surjective K I) le_sup_left
  change J.index=1
  rw [←hidx,htop,Subgroup.index_top]

theorem class_fibre_card_le_one [Finite K] (A : Matrix.SpecialLinearGroup I K)
    (hdet : ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup I K,
      Commute (Matrix.SpecialLinearGroup.toGL A) P ∧ Matrix.GeneralLinearGroup.det P=u) :
    Nat.card {c:ConjClasses (Matrix.SpecialLinearGroup I K) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} ≤
      1 := by
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
  have hb := NormalSubgroupConjugacyFibre.fibre_card_le_join_centralizer_index
    (specialLinearKernel K I) (E A)
  exact (Nat.card_le_card_of_injective embed hinj).trans
    (hb.trans_eq (join_centralizer_index_eq_one K I (E A) hdet))


theorem determinant_surjective_of_conjugate
    (x y g : Matrix.GeneralLinearGroup I K) (hxy : g⁻¹*x*g=y)
    (hdet : ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup I K,
      Commute y P ∧ Matrix.GeneralLinearGroup.det P=u) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup I K,
      Commute x P ∧ Matrix.GeneralLinearGroup.det P=u := by
  intro u
  obtain ⟨P,hP,hD⟩ := hdet u
  refine ⟨g*P*g⁻¹,?_,?_⟩
  · have hx : g*y*g⁻¹=x := by rw [←hxy]; group
    have hh : Commute (g*y*g⁻¹) (g*P*g⁻¹) := hP.map (MulAut.conj g).toMonoidHom
    rw [hx] at hh
    exact hh
  · simp only [map_mul,map_inv,hD]
    simp only [mul_assoc,mul_left_comm,mul_comm,mul_inv_cancel,mul_one]

end SymmetricSubgroupAsymptotics.SpecialLinearCentralizerDeterminantFibre
