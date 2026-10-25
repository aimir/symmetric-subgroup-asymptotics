import SymmetricSubgroupAsymptotics.SLThreeConjugacyClassBound

/-! The two noncyclic scalar keys selected by the proved SL3 normal
form cover are nonzero, because their actual conjugates have determinant
one. Replace those two field branches by units before counting classes.
No matrix, group, or action census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLThreeNonzeroKeyClassBound
open SLThreeNormalFormCover

variable (K : Type*) [Field K]
abbrev Key := (K × K) ⊕ (Kˣ ⊕ Kˣ)

def forgetKey : Key K → SLThreeNormalFormCover.Key K
  | Sum.inl st => Sum.inl st
  | Sum.inr (Sum.inl a) => Sum.inr (Sum.inl a.val)
  | Sum.inr (Sum.inr a) => Sum.inr (Sum.inr a.val)

theorem selected_key_det (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (normalMatrix K (SLThreeConjugacyClassBound.matrixKey K A)).det=1 := by
  obtain ⟨P,hP⟩ := SLThreeConjugacyClassBound.exists_conjugator_for_key K A
  have hh := congrArg Matrix.det hP
  rw [det_conjugate,A.property] at hh
  exact hh.symm

theorem exists_nonzero_key (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ k : Key K, forgetKey K k=SLThreeConjugacyClassBound.matrixKey K A := by
  cases he : SLThreeConjugacyClassBound.matrixKey K A with
  | inl st => exact ⟨Sum.inl st,rfl⟩
  | inr u =>
    have hd : (normalMatrix K (Sum.inr u)).det=1 := by
      simpa only [he] using selected_key_det K A
    cases u with
    | inl a =>
      have ha : a≠0 := by
        intro hz
        change (FiniteThreeNoncyclicConjugacy.diagonal a ((a⁻¹)^2)).det=1 at hd
        rw [diagonal_det,hz] at hd
        simp only [zero_mul,zero_ne_one] at hd
      exact ⟨Sum.inr (Sum.inl (Units.mk0 a ha)),rfl⟩
    | inr a =>
      have ha : a≠0 := by
        intro hz
        change (FiniteThreeNoncyclicConjugacy.jordan a).det=1 at hd
        simp [FiniteThreeNoncyclicConjugacy.jordan,Matrix.det_fin_three,hz] at hd
      exact ⟨Sum.inr (Sum.inr (Units.mk0 a ha)),rfl⟩

def classKey (c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) : Key K :=
  Classical.choose (exists_nonzero_key K (SLThreeConjugacyClassBound.representative K c))

theorem forget_classKey (c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) :
    forgetKey K (classKey K c)=SLThreeConjugacyClassBound.classKey K c :=
  Classical.choose_spec (exists_nonzero_key K (SLThreeConjugacyClassBound.representative K c))

local instance slFinite [Finite K] : Finite (Matrix.SpecialLinearGroup (Fin 3) K) :=
  Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 3) K => A.val)
    Subtype.val_injective

local instance classesFinite [Finite K] :
    Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) :=
  Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 3) K) _)
    ConjClasses.mk_surjective

theorem key_fibre_card_le_gcd [Finite K] (k : Key K) :
    Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} ≤
      (Nat.card K-1).gcd 3 := by
  let f : {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} →
      {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
        SLThreeConjugacyClassBound.classKey K c=forgetKey K k} := fun c =>
    ⟨c.val,by rw [←forget_classKey K c.val,c.property]⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact congrArg (fun z : {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) //
      SLThreeConjugacyClassBound.classKey K c=forgetKey K k} => z.val) he
  exact (Nat.card_le_card_of_injective f hf).trans
    (SLThreeConjugacyClassBound.key_fibre_card_le_gcd K (forgetKey K k))

theorem key_card [Finite K] : Nat.card (Key K)=(Nat.card K)^2+2*(Nat.card K-1) := by
  simp only [Key,Nat.card_sum,Nat.card_prod,Nat.card_units]
  ring

theorem class_card_le [Finite K] :
    Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) ≤
      (Nat.card K-1).gcd 3*((Nat.card K)^2+2*(Nat.card K-1)) := by
  letI : Fintype (Key K) := Fintype.ofFinite _
  calc
    _ = Nat.card (Σ k : Key K,
        {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv (classKey K))).symm
    _ = ∑ k : Key K,
        Nat.card {c : ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K) // classKey K c=k} :=
      Nat.card_sigma
    _ ≤ ∑ _k : Key K, (Nat.card K-1).gcd 3 :=
      Finset.sum_le_sum (fun k _ => key_fibre_card_le_gcd K k)
    _ = Nat.card (Key K)*(Nat.card K-1).gcd 3 := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card,Nat.cast_id]
    _ = _ := by rw [key_card]; exact Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.SLThreeNonzeroKeyClassBound
