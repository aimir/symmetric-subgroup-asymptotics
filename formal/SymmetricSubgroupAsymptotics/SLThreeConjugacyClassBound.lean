import SymmetricSubgroupAsymptotics.SLThreeNormalFormCover
import SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! An actual all-field finite SL3 class bound from literal GL3 normal
forms. A key records two cyclic coefficients, one repeated diagonal
scalar, or one Jordan scalar. Equal keys give actual GL3 conjugacy; the
proved generic GL-to-SL fibre bound charges gcd(q-1,3). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLThreeConjugacyClassBound

open SLThreeNormalFormCover
variable (K : Type*) [Field K]
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) K
abbrev GeneralLinear := Matrix.GeneralLinearGroup (Fin 3) K

def matrixKey (A : SL K) : Key K := Classical.choose (exists_key_conjugator A)

theorem exists_conjugator_for_key (A : SL K) :
    ∃ P : GeneralLinear K, (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A.val *
      (P : Matrix (Fin 3) (Fin 3) K) = normalMatrix K (matrixKey K A) :=
  Classical.choose_spec (exists_key_conjugator A)

theorem isConj_of_key_eq (A B : SL K) (he : matrixKey K A = matrixKey K B) :
    IsConj (Matrix.SpecialLinearGroup.toGL A) (Matrix.SpecialLinearGroup.toGL B) := by
  obtain ⟨P, hP⟩ := exists_conjugator_for_key K A
  obtain ⟨Q, hQ⟩ := exists_conjugator_for_key K B
  let AA : GeneralLinear K := Matrix.SpecialLinearGroup.toGL A
  let BB : GeneralLinear K := Matrix.SpecialLinearGroup.toGL B
  have hh : P⁻¹ * AA * P = Q⁻¹ * BB * Q := by
    apply Units.ext
    change (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A.val *
      (P : Matrix (Fin 3) (Fin 3) K) =
      (↑(Q⁻¹) : Matrix (Fin 3) (Fin 3) K) * B.val *
        (Q : Matrix (Fin 3) (Fin 3) K)
    exact hP.trans ((congrArg (normalMatrix K) he).trans hQ.symm)
  have hA : IsConj AA (P⁻¹ * AA * P) :=
    isConj_iff.mpr ⟨P⁻¹, by simp only [inv_inv]⟩
  have hB : IsConj BB (Q⁻¹ * BB * Q) :=
    isConj_iff.mpr ⟨Q⁻¹, by simp only [inv_inv]⟩
  have hB' : IsConj (P⁻¹ * AA * P) BB := by
    rw [hh]
    exact hB.symm
  exact hA.trans hB'

def representative (c : ConjClasses (SL K)) : SL K :=
  Classical.choose (ConjClasses.exists_rep c)

theorem mk_representative (c : ConjClasses (SL K)) :
    ConjClasses.mk (representative K c) = c := Classical.choose_spec (ConjClasses.exists_rep c)

def classKey (c : ConjClasses (SL K)) : Key K := matrixKey K (representative K c)

local instance slFinite [Finite K] : Finite (SL K) :=
  Finite.of_injective (fun A : SL K => A.val) Subtype.val_injective

local instance classesFinite [Finite K] : Finite (ConjClasses (SL K)) :=
  Finite.of_surjective (@ConjClasses.mk (SL K) _) ConjClasses.mk_surjective

theorem key_fibre_card_le_gcd [Finite K] (k : Key K) :
    Nat.card {c : ConjClasses (SL K) // classKey K c = k} ≤ (Nat.card K - 1).gcd 3 := by
  by_cases he : Nonempty {c : ConjClasses (SL K) // classKey K c = k}
  · obtain ⟨a⟩ := he
    let A := representative K a.val
    let encode : {c : ConjClasses (SL K) // classKey K c = k} →
        {c : ConjClasses (SL K) // ConjClasses.map Matrix.SpecialLinearGroup.toGL c =
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} := fun c => ⟨c.val, by
      rw [← mk_representative K c.val]
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply isConj_of_key_eq K (representative K c.val) A
      exact c.property.trans a.property.symm⟩
    have hi : Function.Injective encode := by
      intro c d h
      apply Subtype.ext
      exact congrArg (fun z : {c : ConjClasses (SL K) //
        ConjClasses.map Matrix.SpecialLinearGroup.toGL c =
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} => z.val) h
    exact (Nat.card_le_card_of_injective encode hi).trans
      (by simpa only [Fintype.card_fin] using
        SpecialLinearConjugacyFibre.class_fibre_card_le_gcd K (Fin 3) A)
  · letI : IsEmpty {c : ConjClasses (SL K) // classKey K c = k} := ⟨fun c => he ⟨c⟩⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

omit [Field K] in
theorem key_card [Finite K] : Nat.card (Key K) = (Nat.card K)^2 + 2 * Nat.card K := by
  simp only [Key, Nat.card_sum, Nat.card_prod]
  ring

theorem class_card_le [Finite K] :
    Nat.card (ConjClasses (SL K)) ≤
      (Nat.card K - 1).gcd 3 * ((Nat.card K)^2 + 2 * Nat.card K) := by
  letI : Fintype (Key K) := Fintype.ofFinite _
  calc
    Nat.card (ConjClasses (SL K)) =
        Nat.card (Σ k : Key K, {c : ConjClasses (SL K) // classKey K c = k}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv (classKey K))).symm
    _ = ∑ k : Key K, Nat.card {c : ConjClasses (SL K) // classKey K c = k} := Nat.card_sigma
    _ ≤ ∑ _k : Key K, (Nat.card K - 1).gcd 3 :=
      Finset.sum_le_sum (fun k _ => key_fibre_card_le_gcd K k)
    _ = Nat.card (Key K) * (Nat.card K - 1).gcd 3 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Nat.cast_id]
    _ = (Nat.card K - 1).gcd 3 * ((Nat.card K)^2 + 2 * Nat.card K) := by
      rw [key_card]
      exact Nat.mul_comm _ _

theorem class_card_le_three_mul [Finite K] :
    Nat.card (ConjClasses (SL K)) ≤ 3 * ((Nat.card K)^2 + 2 * Nat.card K) :=
  (class_card_le K).trans (Nat.mul_le_mul_right _ (Nat.gcd_le_right _ (by decide : 0 < 3)))

theorem class_card_le_of_gcd_eq_one [Finite K] (hg : (Nat.card K - 1).gcd 3 = 1) :
    Nat.card (ConjClasses (SL K)) ≤ (Nat.card K)^2 + 2 * Nat.card K := by
  simpa only [hg, one_mul] using class_card_le K

end SymmetricSubgroupAsymptotics.SLThreeConjugacyClassBound
