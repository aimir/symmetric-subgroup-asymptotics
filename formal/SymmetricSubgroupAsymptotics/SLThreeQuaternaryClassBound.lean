import SymmetricSubgroupAsymptotics.SLThreeNonzeroKeyClassBound
import SymmetricSubgroupAsymptotics.SpecialLinearCentralizerDeterminantFibre
import SymmetricSubgroupAsymptotics.SLThreeNoncyclicDeterminantCentralizers
import SymmetricSubgroupAsymptotics.SLThreeQuaternaryCyclicCentralizer

/-! Weighted counting of the actual SL3 normal-form fibres over a
four-element field. Only the three nonzero cubic scalar cyclic keys
may split into three classes; all other actual fibres cost one. The
exceptional keys are the injective image of field units, not a table.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLThreeQuaternaryClassBound
open SLThreeNonzeroKeyClassBound
variable (K : Type*) [Field K] [Finite K]

local instance slFinite : Finite (Matrix.SpecialLinearGroup (Fin 3) K) :=
  Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 3) K => A.val)
    Subtype.val_injective
local instance classesFinite : Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) :=
  Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 3) K) _)
    ConjClasses.mk_surjective

private theorem key_fibre_card_le_one_of_normal_det (k : Key K)
    (hdet : ∀ Y : Matrix.GeneralLinearGroup (Fin 3) K,
      (Y : Matrix (Fin 3) (Fin 3) K)=SLThreeNormalFormCover.normalMatrix K (forgetKey K k) →
      ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
        Commute Y P ∧ Matrix.GeneralLinearGroup.det P=u) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} ≤ 1 := by
  by_cases he : Nonempty {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k}
  · obtain ⟨c₀⟩ := he
    let A := SLThreeConjugacyClassBound.representative K c₀.val
    obtain ⟨P,hP⟩ := SLThreeConjugacyClassBound.exists_conjugator_for_key K A
    have hkey : SLThreeConjugacyClassBound.matrixKey K A=forgetKey K k := by
      have hh := forget_classKey K c₀.val
      rw [c₀.property] at hh
      exact hh.symm
    let x := Matrix.SpecialLinearGroup.toGL A
    let y := P⁻¹*x*P
    have hy : (y : Matrix (Fin 3) (Fin 3) K)=SLThreeNormalFormCover.normalMatrix K (forgetKey K k) := by
      change (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K)*A.val*(P : Matrix (Fin 3) (Fin 3) K)=_
      exact hP.trans (congrArg (SLThreeNormalFormCover.normalMatrix K) hkey)
    have hd := SpecialLinearCentralizerDeterminantFibre.determinant_surjective_of_conjugate
      K (Fin 3) x y P rfl (hdet y hy)
    let f : {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} →
        {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
          ConjClasses.map Matrix.SpecialLinearGroup.toGL c=ConjClasses.mk x} := fun c => ⟨c.val,by
      rw [←SLThreeConjugacyClassBound.mk_representative K c.val]
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply SLThreeConjugacyClassBound.isConj_of_key_eq K
      have hh := congrArg (forgetKey K) (c.property.trans c₀.property.symm)
      rw [forget_classKey,forget_classKey] at hh
      exact hh⟩
    have hf : Function.Injective f := by
      intro c d hh
      apply Subtype.ext
      exact congrArg (fun z : {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
        ConjClasses.map Matrix.SpecialLinearGroup.toGL c=ConjClasses.mk x} => z.val) hh
    exact (Nat.card_le_card_of_injective f hf).trans
      (SpecialLinearCentralizerDeterminantFibre.class_fibre_card_le_one K (Fin 3) A hd)
  · letI : IsEmpty {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} :=
      ⟨fun c => he ⟨c⟩⟩
    simp only [Nat.card_of_isEmpty,Nat.zero_le]

theorem noncyclic_key_fibre_card_le_one (a : Kˣ ⊕ Kˣ) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
      classKey K c=Sum.inr a} ≤ 1 := by
  apply key_fibre_card_le_one_of_normal_det K (Sum.inr a)
  intro Y hY
  rcases a with a | a
  · exact SLThreeNoncyclicDeterminantCentralizers.diagonal_determinant_surjective
      Y (a : K) (((a : K)⁻¹)^2) hY
  · exact SLThreeNoncyclicDeterminantCentralizers.jordan_determinant_surjective Y (a : K) hY

theorem noncubic_key_fibre_card_le_one [CharP K 2] (hK : Nat.card K=4) (s t : K)
    (h : (s=0 ∧ t=0) ∨ s≠t^2) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
      classKey K c=Sum.inl (s,t)} ≤ 1 := by
  apply key_fibre_card_le_one_of_normal_det K (Sum.inl (s,t))
  intro Y hY
  exact SLThreeQuaternaryCyclicCentralizer.origin_or_noncubic_determinant_surjective hK s t h Y hY

theorem class_card_le_twentyEight [CharP K 2] (hK : Nat.card K=4) :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ 28 := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (Key K) := Fintype.ofFinite _
  let bad : Finset (Key K) := Finset.univ.image (fun u : Kˣ =>
    (Sum.inl ((u : K)^2,(u : K)) : Key K))
  have hi : Function.Injective (fun u : Kˣ => (Sum.inl ((u : K)^2,(u : K)) : Key K)) := by
    intro u v hh
    apply Units.ext
    exact congrArg Prod.snd (Sum.inl.inj hh)
  have hbad : bad.card=3 := by
    rw [Finset.card_image_of_injective _ hi,Finset.card_univ,←Nat.card_eq_fintype_card,
      Nat.card_units,hK]
  have hkey : Fintype.card (Key K)=22 := by
    have hh := key_card K
    simpa only [hK,Nat.card_eq_fintype_card] using hh
  have hcompl : badᶜ.card=19 := by
    have hh := Finset.card_add_card_compl bad
    rw [hbad,hkey] at hh
    omega
  let F : Key K → ℕ := fun k =>
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k}
  have hthree (k : Key K) : F k ≤ 3 := by
    simpa only [F,hK] using key_fibre_card_le_gcd K k
  have hone (k : Key K) (hk : k∉bad) : F k ≤ 1 := by
    rcases k with ⟨s,t⟩ | a
    · apply noncubic_key_fibre_card_le_one K hK s t
      by_cases he : s=t^2
      · by_cases ht : t=0
        · exact Or.inl ⟨by simpa only [ht,zero_pow (by decide : (2:ℕ)≠0)] using he,ht⟩
        · exfalso
          apply hk
          refine Finset.mem_image.mpr ⟨Units.mk0 t ht,Finset.mem_univ _,?_⟩
          change (Sum.inl (t^2,t) : Key K)=Sum.inl (s,t)
          rw [he]
      · exact Or.inr he
    · exact noncyclic_key_fibre_card_le_one K a
  have hsum : Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K))=∑ k, F k := by
    rw [←Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv (classKey K))).symm
  calc
    _ = (∑ k∈bad,F k)+(∑ k∈badᶜ,F k) :=
      hsum.trans (Finset.sum_add_sum_compl bad F).symm
    _ ≤ (∑ _k∈bad,3)+(∑ _k∈badᶜ,1) := Nat.add_le_add
      (Finset.sum_le_sum (fun k _ => hthree k))
      (Finset.sum_le_sum (fun k hk => hone k (Finset.mem_compl.mp hk)))
    _ = 28 := by simp only [Finset.sum_const,nsmul_eq_mul,hbad,hcompl]; decide

end SymmetricSubgroupAsymptotics.SLThreeQuaternaryClassBound
