import SymmetricSubgroupAsymptotics.SLThreeCentralScalarFixedClasses
import SymmetricSubgroupAsymptotics.SLThreeQuaternaryClassBound
import SymmetricSubgroupAsymptotics.CentralOrderThreeConjugacyClasses
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! An actual nonidentity scalar of order three in the original SL3
model, its proved fixed-class ceiling, and the proved SL28 ceiling give
at most ten classes on the SAME full-centre projective quotient. No
class number, centre identification, or action classification is input.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.ProjectiveSLThreeQuaternaryClassBound
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private def scalarCube (u : Kˣ) (hu : u^3=1) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.scalar (Fin 3) (u : K),by
    calc
      _ = (u : K)^3 := by
        simp [Matrix.scalar_apply,Matrix.det_diagonal]
      _ = 1 := by
        have hh := congrArg (fun a : Kˣ => (a : K)) hu
        simpa only [Units.val_pow_eq_pow_val,Units.val_one] using hh⟩

omit [Finite K] [CharP K 2] in
private theorem scalarCube_toGL (u : Kˣ) (hu : u^3=1) :
    Matrix.SpecialLinearGroup.toGL (scalarCube u hu)=Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  apply Units.ext
  rfl

theorem class_card_le_ten (hK : Nat.card K=4) :
    Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) ≤ 10 := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  letI : Finite (Matrix.SpecialLinearGroup (Fin 3) K) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 3) K => A.val)
      Subtype.val_injective
  letI : Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 3) K) _)
      ConjClasses.mk_surjective
  have hUnits : Nat.card Kˣ=3 := by rw [Nat.card_units,hK]
  letI : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUnits]; decide)
  obtain ⟨u,hu⟩ := exists_ne (1 : Kˣ)
  have hu3 : u^3=1 := by
    have hh := pow_card_eq_one (x := u)
    simpa only [←Nat.card_eq_fintype_card,hUnits] using hh
  let z := scalarCube u hu3
  have hz : z∈Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨(u : K),?_,rfl⟩
    have hh := congrArg (fun a : Kˣ => (a : K)) hu3
    simpa only [Fintype.card_fin,Units.val_pow_eq_pow_val,Units.val_one] using hh
  have hzGL : Matrix.SpecialLinearGroup.toGL z=Matrix.GeneralLinearGroup.scalar (Fin 3) u :=
    scalarCube_toGL u hu3
  have hz3 : z^3=1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow,map_one,hzGL,←map_pow,hu3,map_one]
  have hzne : z≠1 := by
    intro he
    apply hu
    apply Units.ext
    have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K => A.val 0 0) he
    simpa [z,scalarCube,Matrix.scalar_apply] using hh
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have horder : orderOf z=3 := orderOf_eq_prime hz3 hzne
  have hfixed := SLThreeCentralScalarFixedClasses.fixed_class_card_le_one z hz u rfl hu
  have hquot := CentralOrderThreeConjugacyClasses.central_quotient_class_bound z hz horder 1 hfixed
  have hSL := SLThreeQuaternaryClassBound.class_card_le_twentyEight K hK
  -- Mathlib defines ProjectiveSpecialLinearGroup as this literal full-centre
  -- quotient. Normalize that checked abbreviation before arithmetic sees it.
  change Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) K ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))) ≤ 10
  omega

end SymmetricSubgroupAsymptotics.ProjectiveSLThreeQuaternaryClassBound
