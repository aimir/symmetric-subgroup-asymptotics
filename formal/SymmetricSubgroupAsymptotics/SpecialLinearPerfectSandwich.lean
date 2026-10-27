import SymmetricSubgroupAsymptotics.DerivedCenterSandwichEquivalence
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! A subgroup between literal SL and GL has derived central quotient PSL
whenever SL is perfect.  Both perfectness ranges needed for untwisted A
are proved: dimension at least three over any field, and any dimension
over a finite field of at least four elements.  No group-order formula,
simple-group recognition, or point-group equality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.SpecialLinearPerfectSandwich
open CFSGTypeAElementaryMatrices CFSGTypeAElementaryGeneration CFSGTypeARootTorus

variable {F : Type*} [Field F]

theorem commutator_eq_top_of_dimension (n : ℕ) (hn : 3 ≤ n) :
    commutator (Matrix.SpecialLinearGroup (Fin n) F) = ⊤ := by
  apply eq_top_of_elementary
  intro i j hij a
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < n)
  have he := elementary_commutator (Ne.symm hki) hkj hij a (1 : F)
  rw [mul_one] at he
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem commutator_eq_top_of_field_card [Finite F] (n : ℕ) (hF : 4 ≤ Nat.card F) :
    commutator (Matrix.SpecialLinearGroup (Fin n) F) = ⊤ := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hs : (g : F)^2 ≠ 1 := CFSGTypeAPrimitiveUnitSquare.square_ne_one hF g hg
  have hd : (g : F)^2-1 ≠ 0 := sub_ne_zero.mpr hs
  apply eq_top_of_elementary
  intro i j hij a
  let t : F := ((g : F)^2-1)⁻¹*a
  have he : ⁅torus hij g,elementary hij t⁆ = elementary hij a := by
    rw [commutatorElement_def,torus_conjugation,elementary_inv,← elementary_add]
    congr 1
    calc
      (g : F)^2*t + -t = ((g : F)^2-1)*t := by ring
      _ = a := by dsimp only [t]; rw [← mul_assoc,mul_inv_cancel₀ hd,one_mul]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable {n : Type*} [Fintype n] [DecidableEq n]

def determinantRestriction (H : Subgroup (Matrix.GeneralLinearGroup n F)) : H →* Fˣ :=
  Matrix.GeneralLinearGroup.det.comp H.subtype

def kernelEquivSpecialLinear (H : Subgroup (Matrix.GeneralLinearGroup n F))
    (hSL : ∀ s : Matrix.SpecialLinearGroup n F, Matrix.SpecialLinearGroup.toGL s ∈ H) :
    (determinantRestriction H).ker ≃* Matrix.SpecialLinearGroup n F where
  toFun x := ⟨x.val.val.val,by
    have hx : Matrix.GeneralLinearGroup.det x.val.val = 1 := x.property
    exact congrArg (fun u : Fˣ => (u : F)) hx⟩
  invFun s := ⟨⟨Matrix.SpecialLinearGroup.toGL s,hSL s⟩,
    Matrix.SpecialLinearGroup.coeToGL_det s⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

def equivOfPerfectSpecialLinear (H : Subgroup (Matrix.GeneralLinearGroup n F))
    (hSL : ∀ s : Matrix.SpecialLinearGroup n F, Matrix.SpecialLinearGroup.toGL s ∈ H)
    [Group.IsPerfect (Matrix.SpecialLinearGroup n F)] :
    DerivedCenterSandwichEquivalence.DerivedCenter H ≃*
      Matrix.ProjectiveSpecialLinearGroup n F := by
  let e := kernelEquivSpecialLinear H hSL
  letI : Group.IsPerfect (determinantRestriction H).ker :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (DerivedCenterSandwichEquivalence.ofPerfectKernel (determinantRestriction H)).trans
    (CFSGCenterQuotientEquiv.equiv e)

def equivOfDimension (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) F))
    (hSL : ∀ s : Matrix.SpecialLinearGroup (Fin n) F,
      Matrix.SpecialLinearGroup.toGL s ∈ H) :
    DerivedCenterSandwichEquivalence.DerivedCenter H ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) F := by
  letI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) F) :=
    ⟨commutator_eq_top_of_dimension n hn⟩
  exact equivOfPerfectSpecialLinear H hSL

def equivOfFieldCard [Finite F] (n : ℕ) (hF : 4 ≤ Nat.card F)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) F))
    (hSL : ∀ s : Matrix.SpecialLinearGroup (Fin n) F,
      Matrix.SpecialLinearGroup.toGL s ∈ H) :
    DerivedCenterSandwichEquivalence.DerivedCenter H ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) F := by
  letI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) F) :=
    ⟨commutator_eq_top_of_field_card n hF⟩
  exact equivOfPerfectSpecialLinear H hSL

end SymmetricSubgroupAsymptotics.SpecialLinearPerfectSandwich
