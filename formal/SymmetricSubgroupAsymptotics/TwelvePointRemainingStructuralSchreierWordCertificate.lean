import SymmetricSubgroupAsymptotics.SchreierKernelGenerators
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralGeneratorTopChart
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralKernelWordCoordinates
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! One finite Schreier/commutator descriptor controls the whole actual
flip kernel. Equality checks concern only the literal twelve-point
permutations. Actual radical membership and original kernel generation
are proved generically, so no normal-subgroup census or stored capacity
is part of the descriptor. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

variable {n : ℕ} (generators : Fin n → Equiv.Perm (Fin 12))

def rawSectionWord (sectionWords : Equiv.Perm (Fin 4) → List (Fin n))
    (q : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 12) := ((sectionWords q).map generators).prod

def rawSchreierWord (codes : Fin n → Equiv.Perm (Fin 4))
    (sectionWords : Equiv.Perm (Fin 4) → List (Fin n))
    (x : Equiv.Perm (Fin 4) × Fin n) : Equiv.Perm (Fin 12) :=
  rawSectionWord generators sectionWords x.1 * generators x.2 *
    (rawSectionWord generators sectionWords (x.1*codes x.2))⁻¹

def rawSchreierSelected (codes : Fin n → Equiv.Perm (Fin 4))
    (sectionWords : Equiv.Perm (Fin 4) → List (Fin n))
    (selected : Option (Equiv.Perm (Fin 4) × Fin n)) : Equiv.Perm (Fin 12) :=
  selected.elim 1 (rawSchreierWord generators codes sectionWords)

def rawSchreierCommutator (codes : Fin n → Equiv.Perm (Fin 4))
    (sectionWords : Equiv.Perm (Fin 4) → List (Fin n))
    (x : (Equiv.Perm (Fin 4) × Fin n) × Fin n) : Equiv.Perm (Fin 12) :=
  ⁅rawSchreierWord generators codes sectionWords x.1,generators x.2⁆

structure SymmetricPairSchreierWordData (D : SymmetricPairGeneratorData generators) where
  sectionWords : Equiv.Perm (Fin 4) → List (Fin n)
  section_eval : ∀ q, ((sectionWords q).map D.codes).prod=q
  section_one : sectionWords 1=[]
  selected : Option (Equiv.Perm (Fin 4) × Fin n)
  coefficient : Equiv.Perm (Fin 4) × Fin n → Bool
  commutators : Equiv.Perm (Fin 4) × Fin n → List ((Equiv.Perm (Fin 4) × Fin n) × Fin n)
  reduction : ∀ x,
    rawSchreierWord generators D.codes sectionWords x *
      (if coefficient x then rawSchreierSelected generators D.codes sectionWords selected else 1)⁻¹ =
        ((commutators x).map (rawSchreierCommutator generators D.codes sectionWords)).prod

namespace SymmetricPairSchreierWordData
variable {generators} {D : SymmetricPairGeneratorData generators}
  (C : SymmetricPairSchreierWordData generators D)

private abbrev G := Subgroup.closure (Set.range generators)

def evalWord (_C : SymmetricPairSchreierWordData generators D) (w : List (Fin n)) : G (generators := generators) :=
  (w.map (closureGenerators generators)).prod

private theorem evalWord_val (w : List (Fin n)) :
    (C.evalWord w : Equiv.Perm (Fin 12))=(w.map generators).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change generators i * (C.evalWord w : Equiv.Perm (Fin 12)) =
      generators i * (w.map generators).prod
    rw [ih]

private theorem beta_evalWord (w : List (Fin n)) :
    D.beta (C.evalWord w)=(w.map D.codes).prod := by
  induction w with
  | nil => exact map_one D.beta
  | cons i w ih =>
    change D.beta (closureGenerators generators i * C.evalWord w)=_
    rw [map_mul,D.beta_generator,ih]
    rfl

def sectionMap (q : Equiv.Perm (Fin 4)) : G (generators := generators) := C.evalWord (C.sectionWords q)

private theorem sectionMap_beta (q : Equiv.Perm (Fin 4)) : D.beta (C.sectionMap q)=q :=
  (C.beta_evalWord _).trans (C.section_eval q)

private theorem sectionMap_one : C.sectionMap 1=1 := by
  change C.evalWord (C.sectionWords 1)=1
  rw [C.section_one]
  rfl

def kernelGenerator (x : Equiv.Perm (Fin 4) × Fin n) : D.frame.top.ker :=
  ⟨schreierWords (G := G (generators := generators)) (closureGenerators generators)
    D.beta C.sectionMap x, by
    rw [← D.beta_kernel]
    apply MonoidHom.mem_ker.mpr
    simp only [schreierWords,map_mul,map_inv,C.sectionMap_beta,mul_inv_cancel]⟩

private theorem kernelGenerator_val (x : Equiv.Perm (Fin 4) × Fin n) :
    ((C.kernelGenerator x : G (generators := generators)) : Equiv.Perm (Fin 12))=
      rawSchreierWord generators D.codes C.sectionWords x := by
  change (C.sectionMap x.1 : Equiv.Perm (Fin 12)) * generators x.2 *
    (C.sectionMap (x.1*D.beta (closureGenerators generators x.2)) : Equiv.Perm (Fin 12))⁻¹=_
  rw [D.beta_generator]
  change (C.evalWord (C.sectionWords x.1) : Equiv.Perm (Fin 12)) * generators x.2 *
    (C.evalWord (C.sectionWords (x.1*D.codes x.2)) : Equiv.Perm (Fin 12))⁻¹=_
  rw [C.evalWord_val,C.evalWord_val]
  rfl

private theorem kernelGenerator_generated :
    Subgroup.closure (Set.range (fun x => (C.kernelGenerator x : G (generators := generators))))=
      D.frame.top.ker :=
  (schreier_kernel_generated (closureGenerators generators) (closureGenerators_full generators)
    D.beta C.sectionMap C.sectionMap_beta C.sectionMap_one).symm.trans D.beta_kernel

def selectedKernel : D.frame.top.ker := C.selected.elim 1 C.kernelGenerator

private theorem selectedKernel_val :
    ((C.selectedKernel : G (generators := generators)) : Equiv.Perm (Fin 12))=
      rawSchreierSelected generators D.codes C.sectionWords C.selected := by
  cases h : C.selected with
  | none =>
    simp only [selectedKernel,rawSchreierSelected,h]
    rfl
  | some x => simpa only [selectedKernel,rawSchreierSelected,h] using C.kernelGenerator_val x

def commutatorElement (x : (Equiv.Perm (Fin 4) × Fin n) × Fin n) : G (generators := generators) :=
  ⁅(C.kernelGenerator x.1 : G (generators := generators)),closureGenerators generators x.2⁆

private theorem commutatorElement_val (x : (Equiv.Perm (Fin 4) × Fin n) × Fin n) :
    (C.commutatorElement x : Equiv.Perm (Fin 12))=
      rawSchreierCommutator generators D.codes C.sectionWords x := by
  change ⁅((C.kernelGenerator x.1 : G (generators := generators)) : Equiv.Perm (Fin 12)),
    generators x.2⁆=_
  rw [C.kernelGenerator_val]
  rfl

private theorem commutatorElement_mem (x : (Equiv.Perm (Fin 4) × Fin n) × Fin n) :
    C.commutatorElement x ∈ primeRelativeRadical 2 D.frame.top.ker :=
  commutator_mem_primeRelativeRadical 2 D.frame.top.ker (C.kernelGenerator x.1)
    (closureGenerators generators x.2)

private theorem product_val (w : List ((Equiv.Perm (Fin 4) × Fin n) × Fin n)) :
    ((w.map C.commutatorElement).prod : Equiv.Perm (Fin 12))=
      (w.map (rawSchreierCommutator generators D.codes C.sectionWords)).prod := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change (C.commutatorElement x : Equiv.Perm (Fin 12)) *
      ((w.map C.commutatorElement).prod : Equiv.Perm (Fin 12))=_
    rw [C.commutatorElement_val,ih]
    rfl

private theorem reduction_mem (x : Equiv.Perm (Fin 4) × Fin n) :
    ((C.kernelGenerator x * (if C.coefficient x then C.selectedKernel else 1)⁻¹ : D.frame.top.ker) :
      G (generators := generators)) ∈ primeRelativeRadical 2 D.frame.top.ker := by
  have he : ((C.kernelGenerator x * (if C.coefficient x then C.selectedKernel else 1)⁻¹ :
      D.frame.top.ker) : G (generators := generators))=
        ((C.commutators x).map C.commutatorElement).prod := by
    apply Subtype.ext
    have hp := C.product_val (C.commutators x)
    have hs := C.selectedKernel_val
    have hg := C.kernelGenerator_val x
    cases hc : C.coefficient x <;>
      simpa only [hc,Bool.false_eq_true,ite_false,ite_true,Subgroup.coe_mul,
        Subgroup.coe_inv,OneMemClass.coe_one,hg,hs,hp] using C.reduction x
  rw [he]
  apply (primeRelativeRadical 2 D.frame.top.ker).list_prod_mem
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact C.commutatorElement_mem i

include C in
/-- All original kernel characters are determined by one actual kernel
value, using only the finite retained commutator word identities. -/
theorem kernel_relative_head_le_one :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 D.frame.top.ker) ≤ 1 := by
  let words : Equiv.Perm (Fin 4) × Fin n → List (Fin 1) :=
    fun x => if C.coefficient x then [0] else []
  apply relativeHead_le_ambient_wordCoordinates 2 D.frame.top.ker C.kernelGenerator
    C.kernelGenerator_generated (fun _ => C.selectedKernel) words
  intro x
  have h := C.reduction_mem x
  cases hc : C.coefficient x <;> simpa only [words,hc,ite_false,ite_true,
    List.map_nil,List.prod_nil,List.map_cons,List.prod_cons,mul_one] using h

end SymmetricPairSchreierWordData
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
