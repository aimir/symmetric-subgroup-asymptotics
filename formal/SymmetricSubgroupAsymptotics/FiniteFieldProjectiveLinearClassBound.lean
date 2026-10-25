import SymmetricSubgroupAsymptotics.FiniteFieldLinearCyclicClassBound
import SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! The finite-field coefficient cover counts literal matrix GL, then
SL via the proved determinant/gcd conjugacy fibre, then the SAME full
central quotient PSL. There is no source recognition or action census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteFieldProjectiveLinearClassBound
variable {K I : Type*} [Field K] [Finite K] [Fintype I] [DecidableEq I] [Nonempty I]

theorem general_class_card_le_coefficients :
    Nat.card (ConjClasses (Matrix.GeneralLinearGroup I K)) ≤
      (Nat.card K-1)*(2*Nat.card K-1)^(Fintype.card I-1) := by
  letI : Fintype K := Fintype.ofFinite K
  let E := Matrix.GeneralLinearGroup.toLin (n := I) (R := K)
  letI : Finite (LinearMap.GeneralLinearGroup K (I → K)) :=
    Finite.of_equiv (Matrix.GeneralLinearGroup I K) E.toEquiv
  have hc := Nat.card_le_card_of_surjective (ConjClasses.map E.symm.toMonoidHom)
    (ConjClasses.map_surjective E.symm.surjective)
  have hd : 0 < Module.finrank K (I → K) := by
    rw [Module.finrank_pi]
    exact Fintype.card_pos
  exact hc.trans (by
    simpa only [Module.finrank_pi] using
      FiniteFieldLinearCyclicClassBound.class_card_le_coefficients (K := K) (V := I → K) hd)

private theorem special_class_card_le_gcd_mul_general :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup I K)) ≤
      (Nat.card K-1).gcd (Fintype.card I)*
        Nat.card (ConjClasses (Matrix.GeneralLinearGroup I K)) := by
  classical
  letI : Finite (Matrix.SpecialLinearGroup I K) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup I K => A.val) Subtype.val_injective
  letI : Fintype (ConjClasses (Matrix.GeneralLinearGroup I K)) := Fintype.ofFinite _
  let f := ConjClasses.map (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup I K →* Matrix.GeneralLinearGroup I K)
  have hfib (c : ConjClasses (Matrix.GeneralLinearGroup I K)) :
      Nat.card {a : ConjClasses (Matrix.SpecialLinearGroup I K) // f a=c} ≤
        (Nat.card K-1).gcd (Fintype.card I) := by
    by_cases he : Nonempty {a : ConjClasses (Matrix.SpecialLinearGroup I K) // f a=c}
    · obtain ⟨a⟩ := he
      obtain ⟨A,hA⟩ := ConjClasses.mk_surjective a.val
      have hc : ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)=c := by
        change f (ConjClasses.mk A)=c
        rw [hA]
        exact a.property
      simpa only [hc] using SpecialLinearConjugacyFibre.class_fibre_card_le_gcd K I A
    · letI : IsEmpty {a : ConjClasses (Matrix.SpecialLinearGroup I K) // f a=c} :=
        ⟨fun a => he ⟨a⟩⟩
      simp only [Nat.card_of_isEmpty,Nat.zero_le]
  calc
    _ = Nat.card (Σ c : ConjClasses (Matrix.GeneralLinearGroup I K),
        {a : ConjClasses (Matrix.SpecialLinearGroup I K) // f a=c}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ c : ConjClasses (Matrix.GeneralLinearGroup I K),
        Nat.card {a : ConjClasses (Matrix.SpecialLinearGroup I K) // f a=c} := Nat.card_sigma
    _ ≤ ∑ _c : ConjClasses (Matrix.GeneralLinearGroup I K),
        (Nat.card K-1).gcd (Fintype.card I) := Finset.sum_le_sum (fun c _ => hfib c)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,
        Nat.cast_id]
      exact Nat.mul_comm _ _

theorem special_class_card_le_coefficients :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup I K)) ≤
      (Nat.card K-1).gcd (Fintype.card I)*
        ((Nat.card K-1)*(2*Nat.card K-1)^(Fintype.card I-1)) :=
  special_class_card_le_gcd_mul_general.trans
    (Nat.mul_le_mul_left _ general_class_card_le_coefficients)

theorem projective_class_card_le_coefficients :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup I K)) ≤
      (Nat.card K-1).gcd (Fintype.card I)*
        ((Nat.card K-1)*(2*Nat.card K-1)^(Fintype.card I-1)) := by
  letI : Finite (Matrix.SpecialLinearGroup I K) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup I K => A.val) Subtype.val_injective
  exact (Nat.card_le_card_of_surjective
    (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup I K))))
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
      special_class_card_le_coefficients

end SymmetricSubgroupAsymptotics.FiniteFieldProjectiveLinearClassBound
