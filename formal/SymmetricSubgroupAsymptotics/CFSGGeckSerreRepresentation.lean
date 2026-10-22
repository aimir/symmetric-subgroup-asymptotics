import SymmetricSubgroupAsymptotics.CFSGFiniteSlTwoSerre
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! A genuine rational Serre representation from an already defined finite
based root pairing. Mathlib's Cartan convention places the acting coroot
in the second argument, so the transpose is kept explicit. This supplies
neither a named exceptional root pairing nor a faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) {n : ℕ} (s : Fin n≃b.support)

 abbrev Target := Matrix (b.support⊕ι) (b.support⊕ι) ℚ
 def cartan : Matrix (Fin n) (Fin n) ℤ := fun i j=>b.cartanMatrix (s j) (s i)
 def H (i : Fin n) : Target b := RootPairing.GeckConstruction.h (s i)
 def E (i : Fin n) : Target b := RootPairing.GeckConstruction.e (s i)
 def F (i : Fin n) : Target b := RootPairing.GeckConstruction.f (s i)

 theorem cartan_is_reindexed_transpose : cartan b s=
    b.cartanMatrix.transpose.submatrix s s := rfl

 theorem HH (i j : Fin n) : ⁅H b s i,H b s j⁆=0 :=
  RootPairing.GeckConstruction.lie_h_h (s i) (s j)

 theorem EF (i j : Fin n) : ⁅E b s i,F b s j⁆=if i=j then H b s i else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact RootPairing.GeckConstruction.lie_e_f_same (s i)
  · rw [if_neg hij]
    exact RootPairing.GeckConstruction.lie_e_f_ne (s.injective.ne hij)

 theorem HE (i j : Fin n) : ⁅H b s i,E b s j⁆=cartan b s i j • E b s j :=
  RootPairing.GeckConstruction.lie_h_e (s j) (s i)

 theorem HF (i j : Fin n) : ⁅H b s i,F b s j⁆= -(cartan b s i j • F b s j) := by
  simpa only [neg_smul] using RootPairing.GeckConstruction.lie_h_f (s j) (s i)

 theorem serreE (i j : Fin n) :
    (LieAlgebra.ad ℚ (Target b) (E b s i)^(-cartan b s i j).toNat) ⁅E b s i,E b s j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have ha : cartan b s i j≤0 :=
      b.cartanMatrix_le_zero_of_ne (s j) (s i) (s.injective.ne (Ne.symm hij))
    have hf : ⁅F b s i,E b s j⁆=0 := by
      have hef : ⁅E b s j,F b s i⁆=0 := by rw [EF,if_neg (Ne.symm hij)]
      calc
        ⁅F b s i,E b s j⁆= -⁅E b s j,F b s i⁆ := (lie_skew _ _).symm
        _=0 := by rw [hef,neg_zero]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight
      (RootPairing.GeckConstruction.isSl2Triple (s i)) (E b s j) (cartan b s i j)
      ha (HE b s i j) hf

 theorem serreF (i j : Fin n) :
    (LieAlgebra.ad ℚ (Target b) (F b s i)^(-cartan b s i j).toNat) ⁅F b s i,F b s j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have ha : cartan b s i j≤0 :=
      b.cartanMatrix_le_zero_of_ne (s j) (s i) (s.injective.ne (Ne.symm hij))
    have hh : ⁅-(H b s i),F b s j⁆=cartan b s i j • F b s j := by
      rw [neg_lie,HF,neg_neg]
    have he : ⁅E b s i,F b s j⁆=0 := by rw [EF,if_neg hij]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight
      (RootPairing.GeckConstruction.isSl2Triple (s i)).symm (F b s j) (cartan b s i j)
      ha hh he

 def rationalRepresentation : CFSG.Models.Chevalley.RationalLie (cartan b s)→ₗ⁅ℚ⁆Target b :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (H b s) (E b s) (F b s) (cartan b s)
    (HH b s) (EF b s) (HE b s) (HF b s) (serreE b s) (serreF b s)

@[simp] theorem rationalRepresentation_H (i : Fin n) :
    rationalRepresentation b s (CFSG.Models.Chevalley.generator (cartan b s)
      (CartanMatrix.Generators.H i))=H b s i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_E (i : Fin n) :
    rationalRepresentation b s (CFSG.Models.Chevalley.generator (cartan b s)
      (CartanMatrix.Generators.E i))=E b s i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_F (i : Fin n) :
    rationalRepresentation b s (CFSG.Models.Chevalley.generator (cartan b s)
      (CartanMatrix.Generators.F i))=F b s i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation
