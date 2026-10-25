import SymmetricSubgroupAsymptotics.SLThreeTraceZeroOriginKey
import SymmetricSubgroupAsymptotics.SLThreeCharacteristicTwoOriginCentralizer
import SymmetricSubgroupAsymptotics.SpecialLinearCentralizerDeterminantFibre
import SymmetricSubgroupAsymptotics.CentralInvolutionConjugacyClasses

/-! A nontrivial literal central scalar in SL3 in characteristic two
fixes at most one conjugacy class. The SAME fixed class has trace and
inverse trace zero, hence lies in the origin GL fibre whose actual
centralizer determinant is surjective. No class-count premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.SLThreeCentralScalarFixedClasses
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) K
private abbrev groupGL := Matrix.GeneralLinearGroup (Fin 3) K

private theorem trace_eq_of_isConj (A B : SL (K := K)) (h : IsConj A B) :
    A.val.trace=B.val.trace := by
  have he := congrArg (ConjClasses.map Matrix.SpecialLinearGroup.toGL)
    (ConjClasses.mk_eq_mk_iff_isConj.mpr h)
  have hc : IsConj (Matrix.SpecialLinearGroup.toGL A) (Matrix.SpecialLinearGroup.toGL B) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp he
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hh := congrArg (fun x : groupGL (K := K) => (x : Matrix (Fin 3) (Fin 3) K).trace) hg
  change ((g : Matrix (Fin 3) (Fin 3) K)*A.val*(↑(g⁻¹) : Matrix (Fin 3) (Fin 3) K)).trace=
    B.val.trace at hh
  rw [Matrix.trace_units_conj] at hh
  exact hh

private theorem inverse_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    IsConj a⁻¹ b⁻¹ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  apply isConj_iff.mpr
  refine ⟨g,?_⟩
  calc
    g*a⁻¹*g⁻¹=(g*a*g⁻¹)⁻¹ := by group
    _ = b⁻¹ := congrArg Inv.inv hg

private theorem trace_zero_of_scalar_conjugacy
    (z A : SL (K := K)) (u : Kˣ)
    (hs : z.val=Matrix.scalar (Fin 3) (u : K)) (hu : u≠1)
    (h : IsConj (z*A) A) : A.val.trace=0 := by
  have hh := trace_eq_of_isConj (z*A) A h
  change (z.val*A.val).trace=A.val.trace at hh
  rw [hs,Matrix.scalar_apply,←Matrix.smul_eq_diagonal_mul,Matrix.trace_smul,smul_eq_mul] at hh
  have hzero : ((u : K)-1)*A.val.trace=0 := by
    calc
      _ = (u : K)*A.val.trace-A.val.trace := by ring
      _ = 0 := by rw [hh,sub_self]
  have hune : (u : K)≠1 := by intro he; apply hu; exact Units.ext he
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hune)

theorem fixed_class_card_le_one
    (z : SL (K := K)) (hz : z∈Subgroup.center (SL (K := K)))
    (u : Kˣ) (hs : z.val=Matrix.scalar (Fin 3) (u : K)) (hu : u≠1) :
    Nat.card {c : ConjClasses (SL (K := K)) //
      CentralInvolutionConjugacyClasses.translate z hz c=c} ≤ 1 := by
  letI : Finite (SL (K := K)) :=
    Finite.of_injective (fun A : SL (K := K) => A.val) Subtype.val_injective
  letI : Finite (ConjClasses (SL (K := K))) :=
    Finite.of_surjective (@ConjClasses.mk (SL (K := K)) _) ConjClasses.mk_surjective
  let O : SL (K := K) := ⟨FiniteThreeCyclicCompanion.companion ![1,0,0],
    SLThreeNormalFormCover.companion_det _⟩
  have hzGL : Matrix.SpecialLinearGroup.toGL z=Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    apply Units.ext
    exact hs
  have hzinv : (z⁻¹).val=Matrix.scalar (Fin 3) (↑(u⁻¹) : K) := by
    have hh : Matrix.SpecialLinearGroup.toGL (z⁻¹)=
        Matrix.GeneralLinearGroup.scalar (Fin 3) (u⁻¹) := by
      rw [map_inv,hzGL,←map_inv]
    exact congrArg (fun g : groupGL (K := K) => (g : Matrix (Fin 3) (Fin 3) K)) hh
  let f : {c : ConjClasses (SL (K := K)) //
      CentralInvolutionConjugacyClasses.translate z hz c=c} →
      {c : ConjClasses (SL (K := K)) // ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL O)} := fun c => ⟨c.val,by
    let A := SLThreeConjugacyClassBound.representative K c.val
    have hm : ConjClasses.mk A=c.val := SLThreeConjugacyClassBound.mk_representative K c.val
    have hh : CentralInvolutionConjugacyClasses.translate z hz (ConjClasses.mk A)=
        ConjClasses.mk A := by rw [hm]; exact c.property
    change ConjClasses.mk (z*A)=ConjClasses.mk A at hh
    have hc : IsConj (z*A) A := ConjClasses.mk_eq_mk_iff_isConj.mp hh
    have ht : A.val.trace=0 := trace_zero_of_scalar_conjugacy z A u hs hu hc
    have hcInv := inverse_isConj hc
    have hcomm : A⁻¹*z⁻¹=z⁻¹*A⁻¹ :=
      Subgroup.mem_center_iff.mp ((Subgroup.center (SL (K := K))).inv_mem hz) A⁻¹
    rw [mul_inv_rev,hcomm] at hcInv
    have hi : (A⁻¹).val.trace=0 := trace_zero_of_scalar_conjugacy (z⁻¹) (A⁻¹) (u⁻¹)
      hzinv (by intro he; exact hu (inv_eq_one.mp he)) hcInv
    obtain ⟨P,hP⟩ := SLThreeTraceZeroOriginKey.exists_origin_conjugator A ht hi
    rw [←hm]
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_iff.mpr
    refine ⟨P⁻¹,?_⟩
    apply Units.ext
    change (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K)*A.val*
      (↑((P⁻¹)⁻¹) : Matrix (Fin 3) (Fin 3) K)=O.val
    simpa only [inv_inv] using hP⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact congrArg (fun a : {c : ConjClasses (SL (K := K)) //
      ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
        ConjClasses.mk (Matrix.SpecialLinearGroup.toGL O)} => a.val) he
  exact (Nat.card_le_card_of_injective f hf).trans
    (SpecialLinearCentralizerDeterminantFibre.class_fibre_card_le_one K (Fin 3) O
      (SLThreeCharacteristicTwoOriginCentralizer.determinant_surjective
        (Matrix.SpecialLinearGroup.toGL O) rfl))

end SymmetricSubgroupAsymptotics.SLThreeCentralScalarFixedClasses
