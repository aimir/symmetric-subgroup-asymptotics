import SymmetricSubgroupAsymptotics.CFSGSerreSparseRootFamilyCertificate
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyParents
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleActionEntries

/-! The actual-source binding for the finite F4 integer certificate.
All rational source weights, simple/Cartan base actions and twenty
nonzero parent paths are discharged from original Serre identities.
Only finite integer coefficient conditions remain inputs here; their
unconditional assembly is a separate theorem. This intermediate binding
asserts neither spanning nor original-model faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSparseFamilyInstaller
open CFSG.Models.Chevalley CFSGIntegralRootActionEntries
open CFSGFFourOriginalRootFamilyProfile CFSGFFourOriginalRootFamilyParents
open CFSGFFourOriginalSimpleActionEntries CFSGSerreSparseRootFamilyCertificate
local notation "A" => CartanMatrix.F₄

private theorem nonsimple_indices : ∀j:Fin 24,1<rootHeight j→
    ∃t:Fin 20,childIndex t=j := by decide +kernel

theorem source_tables_of_integer_certificate (neg:Bool) (E F:Fin 4→Slot→Slot×ℤ)
    (hEcartan:∀i b,E i (.inr b)=cartanRaise i b)
    (hFsimple:∀a i,F a (.inl (simpleIndex i))=simpleLower a i)
    (hEparent:∀t:Fin 20,E (parentNode t) (.inl (parentIndex t))=
      (.inl (childIndex t),parentCoefficient t))
    (hFheight:∀a j,0<height j→(F a j).2≠0→height (F a j).1+1=height j)
    (hEheight:∀i j,0<height j→(E i j).2≠0→height (E i j).1=height j+1)
    (hEweight:∀i a j,0<height j→(E i j).2≠0→
      integerWeight a (E i j).1=A a i+integerWeight a j)
    (hcomm:∀i a j,0<height j→
      (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
        (F a j).2 • integerRow (E i (F a j).1)=
        (E i j).2 • integerRow (F a (E i j).1)) :
    (∀i j,⁅rootVector A neg i,family neg j⁆=
      ((E i j).2:ℚ) • family neg (E i j).1) ∧
      (∀a j,0<height j→
        ⁅CFSGSerreSignedRootWeights.oppositeVector A neg a,family neg j⁆=
          ((F a j).2:ℚ) • family neg (F a j).1) := by
  apply source_tables_of_integer_entries A (family neg) neg height integerWeight E F
    (by decide +kernel) (family_weight neg) ?_ ?_ hFheight hEheight hEweight
    positive_comparison ?_ hcomm
  · intro i j hj
    obtain ⟨b,rfl⟩:=height_zero_is_cartan j hj
    rw [hEcartan]
    simpa only [combination_rationalRow] using cartan_source_raise neg i b
  · intro a j hj
    obtain ⟨i,rfl⟩:=height_one_is_simple j hj
    rw [hFsimple]
    simpa only [combination_rationalRow] using simple_source_lower neg a i
  · intro j hj
    cases j with
    | inl j=>
      obtain ⟨t,rfl⟩:=nonsimple_indices j hj
      refine ⟨parentNode t,.inl (parentIndex t),parentCoefficient t,
        parent_coefficient_ne_zero t,rootHeight_positive (parentIndex t),
        parent_height t,?_,hEparent t⟩
      exact source_parent neg t
    | inr b=>exact (by change 1<0 at hj;omega)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSparseFamilyInstaller
