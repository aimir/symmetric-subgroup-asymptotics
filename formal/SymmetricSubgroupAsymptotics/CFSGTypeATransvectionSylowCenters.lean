import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionHighestRoot
import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularCenter
import SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition

/-! A concrete nonidentity transvection in the original finite SL group
lies in the centre of an actual defining-characteristic Sylow subgroup.
The subgroup is transported by the proved linear-conjugation automorphism,
with its centre preserved by the same original subgroup isomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSylowCenters
open Matrix Module LinearMap CFSGTypeAProjectivePointRoots CFSGTypeAElementaryMatrices
open CFSGSylowCenterRecognition CFSGTypeATransvectionHighestRoot
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

 theorem highestRoot_mem_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 2≤n) :
    elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) (1 : F)∈
      sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p := by
  let P := CFSGTypeAGoodSylow.actualUpperSylow F p n
  let z : P :=
    ⟨elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) 1,
      CFSGUpperUnitriangular.elementary_mem_upperUnitriangular
        (show (⟨0,by omega⟩ : Fin n)<⟨n-1,by omega⟩ by change 0 < n-1;omega) 1⟩
  refine ⟨P,z,?_,rfl⟩
  exact CFSGUpperUnitriangular.highestRoot_mem_center_upperUnitriangular hn 1

theorem transvection_mem_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 2≤n)
    (f : Dual F (Fin n→F)) (v : Fin n→F) (hfv : f v=0) (hf : f≠0) (hv : v≠0) :
    transvectionSL hfv∈sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p := by
  obtain ⟨e,he⟩ := exists_linearConjugation_highestRoot hn f v hfv hf hv
  have hh : linearConjugation e (transvectionSL hfv)∈
      sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p := by
    rw [he]
    exact highestRoot_mem_sylowCenterElements p hn
  exact (automorphism_mem_sylowCenterElements_iff p (linearConjugation e) _).mp hh

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSylowCenters
