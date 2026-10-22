import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeRootLines
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineSymmetries

/-! Two actual negative directions are obtained from U by the original
signed D Coxeter word. Signs are absorbed in the original field
parameters; this is not a permutation-only replacement of the word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCoxeterOpposition
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineSymmetries
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationCoxeterMonomial
open CFSGOrthogonalDIndexOppositeRootLines
variable (K : Type) [Field K]

theorem coxeter_image_line (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hU : (ambientUnipotent K (s + 4)).map
      (MulAut.conj (coxeterWeyl K (s + 3)).val).toMonoidHom ≤ H)
    (a b : Index (s + 4))
    (hline : HasRootLine (ambientUnipotent K (s + 4)) (rootArray K a b)) :
    HasRootLine H (rootArray K (cyclePerm (s + 2) a) (cyclePerm (s + 2) b)) := by
  apply conjugate_line_in K H (ambientUnipotent K (s + 4))
    (coxeterWeyl K (s + 3)).val hU _ _
    (coxeterColumnSign K (s + 2) a / coxeterColumnSign K (s + 2) b)
    (div_ne_zero (coxeterColumnSign_ne_zero K (s + 2) a)
      (coxeterColumnSign_ne_zero K (s + 2) b)) _ hline
  intro t
  rw [coxeter_conjugation, div_mul_eq_mul_div]

theorem coxeter_negative_lines (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hU : (ambientUnipotent K (s + 4)).map
      (MulAut.conj (coxeterWeyl K (s + 3)).val).toMonoidHom ≤ H) :
    HasRootLine H (chainArray (Fin.last (s + 3)) (0 : Fin (s + 4))) ∧
      HasRootLine H (minusArray (0 : Fin (s + 4)) (Fin.last (s + 3))) := by
  let p : Fin (s + 4) := (Fin.last (s + 2)).castSucc
  let l : Fin (s + 4) := Fin.last (s + 3)
  have hpl : p < l := by change s + 2 < s + 3; omega
  have hc := positive_chain_line K (s + 4) p l hpl
  change HasRootLine (ambientUnipotent K (s + 4))
    (rootArray K (Sum.inl p) (Sum.inl l)) at hc
  have hc' := coxeter_image_line K s H hU (Sum.inl p) (Sum.inl l) hc
  change HasRootLine H (rootArray K
    (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 2)).castSucc))
    (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 3))))) at hc'
  rw [cyclePerm_positive_penultimate, cyclePerm_positive_last] at hc'
  have hc'' := paired_line_transfer K H _ _ hc'
  change HasRootLine H (chainArray (Fin.last (s + 3)) (0 : Fin (s + 4))) at hc''
  have hp := positive_plus_line K s p l (ne_of_lt hpl)
  change HasRootLine (ambientUnipotent K (s + 4))
    (rootArray K (Sum.inl p) (Sum.inr l)) at hp
  have hp' := coxeter_image_line K s H hU (Sum.inl p) (Sum.inr l) hp
  change HasRootLine H (rootArray K
    (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 2)).castSucc))
    (cyclePerm (s + 2) (Sum.inr (Fin.last (s + 3))))) at hp'
  rw [cyclePerm_positive_penultimate, cyclePerm_negative_last] at hp'
  have hp'' := paired_line_transfer K H _ _ hp'
  have hm : HasRootLine H (minusArray (0 : Fin (s + 4)) (Fin.last (s + 3))) := by
    intro a
    obtain ⟨g, hg, he⟩ := hp'' a
    exact ⟨g, hg, he.trans (minusArray_eq_rootArray K 0 (Fin.last (s + 3)) a).symm⟩
  exact ⟨hc'', hm⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCoxeterOpposition
