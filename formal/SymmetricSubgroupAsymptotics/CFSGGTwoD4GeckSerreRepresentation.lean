import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries
import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence

/-! A genuine rational representation of the ORIGINAL G2 Serre quotient
in the literal folded D4 Geck matrices. Both Serre powers follow from
actual finite-dimensional sl2 triples. This constructs the rational map,
not an integral/group action comparison or source faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSerreRepresentation
open CFSGGTwoD4GeckGenerators CFSGTrialityD4NormTwo CFSGNormTwoGeckColumns
open CFSG.Models.Chevalley

theorem d4E_selected_entry (i j : Fin 4) :
    d4E i (.inl (Index j))
      (.inr (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (Index j)))=if j=i then 1 else 0 := by
  change RootPairing.GeckConstruction.e (Index i) _ _=_
  rw [CFSGNormTwoGeckNormalizedEntries.E_inl_inr (CartanMatrix.D 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite Base (Index i) (Index j)]
  by_cases h : j=i
  · subst j
    simp
  · simp [h,Index.injective.ne h]

theorem positive_selected_entry (i : Fin 2) :
    positive i (.inl (Index (representative i)))
      (.inr (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (Index (representative i))))=1 := by
  fin_cases i <;> norm_num [positive,representative,Matrix.add_apply,d4E_selected_entry,Fin.ext_iff]

theorem positive_ne_zero (i : Fin 2) : positive i≠0 := by
  intro h
  have hh := congrArg (fun M : Mat=>M (.inl (Index (representative i)))
    (.inr (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (Index (representative i))))) h
  dsimp only at hh
  rw [positive_selected_entry,Matrix.zero_apply] at hh
  exact one_ne_zero hh

theorem cartan_ne_zero (i : Fin 2) : cartan i≠0 := by
  intro h
  have hh := HE i i
  rw [h,zero_lie,CartanMatrix.G₂_diag] at hh
  have he : (2:ℚ) • positive i=0 := by
    simpa only [two_smul] using hh.symm
  exact positive_ne_zero i ((smul_eq_zero.mp he).resolve_left (by norm_num))

def sl2Triple (i : Fin 2) : IsSl2Triple (cartan i) (positive i) (negative i) where
  h_ne_zero := cartan_ne_zero i
  lie_e_f := by simpa only [if_pos rfl] using EF i i
  lie_h_e_nsmul := by simpa only [CartanMatrix.G₂_diag,two_smul] using HE i i
  lie_h_f_nsmul := by simpa only [CartanMatrix.G₂_diag,two_smul] using HF i i

theorem positive_serre (i j : Fin 2) :
    (LieAlgebra.ad ℚ Mat (positive i)^(-CartanMatrix.G₂ i j).toNat) ⁅positive i,positive j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have hf : ⁅negative i,positive j⁆=0 := by
      have hh : ⁅positive j,negative i⁆=0 := by rw [EF,if_neg (Ne.symm hij)]
      calc
        _= -⁅positive j,negative i⁆ := (lie_skew _ _).symm
        _=0 := by rw [hh,neg_zero]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight (sl2Triple i) (positive j)
      (CartanMatrix.G₂ i j) (CartanMatrix.G₂_off_diag_nonpos i j hij) (HE i j) hf

theorem negative_serre (i j : Fin 2) :
    (LieAlgebra.ad ℚ Mat (negative i)^(-CartanMatrix.G₂ i j).toNat) ⁅negative i,negative j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have hh : ⁅-(cartan i),negative j⁆=CartanMatrix.G₂ i j • negative j := by
      rw [neg_lie,HF,neg_neg]
    have he : ⁅positive i,negative j⁆=0 := by rw [EF,if_neg hij]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight (sl2Triple i).symm (negative j)
      (CartanMatrix.G₂ i j) (CartanMatrix.G₂_off_diag_nonpos i j hij) hh he

def rationalRepresentation : RationalLie CartanMatrix.G₂→ₗ⁅ℚ⁆Mat :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    cartan positive negative CartanMatrix.G₂ HH EF HE HF positive_serre negative_serre

@[simp] theorem rationalRepresentation_H (i : Fin 2) :
    rationalRepresentation (generator CartanMatrix.G₂ (CartanMatrix.Generators.H i))=cartan i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_E (i : Fin 2) :
    rationalRepresentation (generator CartanMatrix.G₂ (CartanMatrix.Generators.E i))=positive i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_F (i : Fin 2) :
    rationalRepresentation (generator CartanMatrix.G₂ (CartanMatrix.Generators.F i))=negative i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

private theorem positive_mem_geck (i : Fin 2) :
    positive i∈RootPairing.GeckConstruction.lieAlgebra Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra Base
  have he (j : Fin 4) : d4E j∈T := RootPairing.GeckConstruction.e_mem_lieAlgebra (Index j)
  fin_cases i
  · exact T.add_mem (T.add_mem (he 0) (he 2)) (he 3)
  · exact he 1

private theorem negative_mem_geck (i : Fin 2) :
    negative i∈RootPairing.GeckConstruction.lieAlgebra Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra Base
  have hf (j : Fin 4) : d4F j∈T := RootPairing.GeckConstruction.f_mem_lieAlgebra (Index j)
  fin_cases i
  · exact T.add_mem (T.add_mem (hf 0) (hf 2)) (hf 3)
  · exact hf 1

theorem rational_image_mem_geck (x : RationalLie CartanMatrix.G₂) :
    rationalRepresentation x∈RootPairing.GeckConstruction.lieAlgebra Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra Base
  let S := T.comap rationalRepresentation
  have hle : LieSubalgebra.lieSpan ℚ _ (Set.range (generator CartanMatrix.G₂))≤S := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨g,rfl⟩
    change rationalRepresentation (generator CartanMatrix.G₂ g)∈T
    cases g with
    | H i=>
      rw [rationalRepresentation_H]
      have he : ⁅positive i,negative i⁆=cartan i := by simpa only [if_pos rfl] using EF i i
      rw [←he]
      exact T.lie_mem (positive_mem_geck i) (negative_mem_geck i)
    | E i=>rw [rationalRepresentation_E];exact positive_mem_geck i
    | F i=>rw [rationalRepresentation_F];exact negative_mem_geck i
  rw [CFSGSerreLocalNilpotence.generator_lieSpan_eq_top] at hle
  exact hle (LieSubalgebra.mem_top x)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSerreRepresentation
