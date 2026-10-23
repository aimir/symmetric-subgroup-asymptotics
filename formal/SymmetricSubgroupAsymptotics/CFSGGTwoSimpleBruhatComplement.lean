import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleWeylTransport
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveCoordinateKernels

/-! The two actual coordinate-kernel complements are carried back into
U6 by their simple Weyl words. This discharges the complement-normalization
input of the generic local Bruhat multiplication lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSimpleBruhatComplement
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveSixWord
open CFSGGTwoPositiveWordSubgroup CFSGGTwoPositiveCoordinateKernels
open CFSGGTwoOriginalPositiveCollecting CFSGGTwoOriginalSimpleWeylTransport
variable (K : Type) [Field K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

private theorem root_mem (j : Fin 6) (a : K) : positiveModel K j a∈positiveWordGroup K :=
  (positiveElement K j a).property

theorem short_complement_positive (g : Model A K) (hg : g∈complement K 0) :
    shortWord K*g*(shortWord K)⁻¹∈positiveWordGroup K := by
  obtain ⟨x,hx,hzero⟩ := (mem_complement_iff K 0 g).mp hg
  have hx0 : x 0=0 := hzero
  let c : MulAut (Model A K) := MulAut.conj (shortWord K)
  have hc (j : Fin 6) (a : K) : c (positiveModel K j a)=shortImage K j a :=
    short_transport K j a
  change c g∈positiveWordGroup K
  rw [←hx]
  simp only [modelWord,map_mul,hx0,positiveModel_zero,map_one,one_mul]
  simp only [hc,shortImage]
  exact (positiveWordGroup K).mul_mem
    ((positiveWordGroup K).mul_mem
      ((positiveWordGroup K).mul_mem
        ((positiveWordGroup K).mul_mem (root_mem K 4 (x 1)) (root_mem K 3 (x 2)))
        (root_mem K 2 (-x 3))) (root_mem K 1 (-x 4))) (root_mem K 5 (x 5))

theorem long_complement_positive (g : Model A K) (hg : g∈complement K 1) :
    longWord K*g*(longWord K)⁻¹∈positiveWordGroup K := by
  obtain ⟨x,hx,hzero⟩ := (mem_complement_iff K 1 g).mp hg
  have hx1 : x 1=0 := hzero
  let c : MulAut (Model A K) := MulAut.conj (longWord K)
  have hc (j : Fin 6) (a : K) : c (positiveModel K j a)=longImage K j a :=
    long_transport K j a
  change c g∈positiveWordGroup K
  rw [←hx]
  simp only [modelWord,map_mul,hx1,positiveModel_zero,map_one,mul_one]
  simp only [hc,longImage]
  exact (positiveWordGroup K).mul_mem
    ((positiveWordGroup K).mul_mem
      ((positiveWordGroup K).mul_mem
        ((positiveWordGroup K).mul_mem (root_mem K 2 (x 0)) (root_mem K 0 (-x 2)))
        (root_mem K 3 (x 3))) (root_mem K 5 (x 4))) (root_mem K 4 (-x 5))

def simpleWeyl (i : Fin 2) : Model A K := if i=0 then shortWord K else longWord K

theorem complement_positive (i : Fin 2) (g : Model A K) (hg : g∈complement K i) :
    simpleWeyl K i*g*(simpleWeyl K i)⁻¹∈positiveWordGroup K := by
  fin_cases i
  · exact short_complement_positive K g hg
  · exact long_complement_positive K g hg

end SymmetricSubgroupAsymptotics.CFSGGTwoSimpleBruhatComplement
