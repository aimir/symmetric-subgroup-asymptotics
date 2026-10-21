import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare
import SymmetricSubgroupAsymptotics.CFSGRootSubgroupExtraction
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Actual two-generation of SL₂ and PSL₂ over every finite field of
cardinality at least four. Both generators are displayed words in literal
matrices. The proof extracts a nonzero upper root by a double commutator,
then uses the primitive diagonal torus to obtain every scalar parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeASLTwoGeneration
open CFSGTypeAElementaryMatrices CFSGTypeARootTorus CFSGTypeASLTwoWeyl
variable {F : Type*} [Field F] [Finite F]

/-- Every subgroup containing the displayed torus and twisted Weyl word
is the entire literal special linear group. -/
theorem eq_top_of_torus_twisted_weyl (hcard : 4≤Nat.card F) (g : Fˣ)
    (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g)
    (H : Subgroup (SL2 (F:=F)))
    (hT : torus (by decide : (0 : Fin 2)≠1) g∈H)
    (hS : upper 1*weyl∈H) : H=⊤ := by
  let hij : (0 : Fin 2)≠1 := by decide
  let h : SL2 (F:=F) := torus hij g
  let k : F := (g : F)^2
  let l : F := ((g⁻¹ : Fˣ) : F)^2
  have hAdd : ∀ a b : F,upper (a+b)=upper a*upper b :=
    fun a b => elementary_add hij a b
  have hZero : upper (0 : F)=1 := elementary_zero hij
  have hScale : ∀ a : F,h*upper a*h⁻¹=upper (k*a) :=
    fun a => torus_conjugation hij g a
  have hScale' : ∀ a : F,(weyl*h*weyl⁻¹)*upper a*(weyl*h*weyl⁻¹)⁻¹=
      upper (l*a) := by
    intro a
    dsimp only [h]
    rw [weyl_torus]
    exact torus_conjugation hij g⁻¹ a
  have hComm : Commute (weyl*h*weyl⁻¹) h := by
    have he : weyl*h*weyl⁻¹=h⁻¹ := by
      dsimp only [h]
      rw [weyl_torus,torus_inv]
    rw [he]
    change h⁻¹*h=h*h⁻¹
    simp
  let m : F := (1-l)*(1-k)
  have hm : m≠0 := by
    apply mul_ne_zero
    · exact sub_ne_zero.mpr (Ne.symm (CFSGTypeAPrimitiveUnitSquare.inverse_square_ne_one hcard g hg))
    · exact sub_ne_zero.mpr (Ne.symm (CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard g hg))
  have hM : upper m∈H :=
    CFSGRootSubgroupExtraction.root_mem_of_twisted_torus upper hAdd hZero h weyl
      k l hScale hScale' hComm H hT hS
  have hUpper : ∀ a : F,upper a∈H :=
    all_parameters_of_torus H hij g hg hT m hm hM
  have hW : weyl∈H := by
    have hm' := H.mul_mem (H.inv_mem (hUpper 1)) hS
    simpa only [←mul_assoc,inv_mul_cancel,one_mul] using hm'
  have hLower : ∀ a : F,lower a∈H := by
    intro a
    have hm' := H.mul_mem (H.mul_mem hW (hUpper (-a))) (H.inv_mem hW)
    rw [weyl_upper,neg_neg] at hm'
    exact hm'
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary H
  intro i j hij' a
  fin_cases i <;> fin_cases j
  · exact (hij' rfl).elim
  · exact hUpper a
  · exact hLower a
  · exact (hij' rfl).elim

/-- The two actual matrices generate SL₂. -/
theorem exists_generating_pair (hcard : 4≤Nat.card F) :
    ∃ x y : SL2 (F:=F),Subgroup.closure ({x,y} : Set (SL2 (F:=F)))=⊤ := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Fˣ)
  let x : SL2 (F:=F) := torus (by decide : (0 : Fin 2)≠1) g
  let y : SL2 (F:=F) := upper 1*weyl
  refine ⟨x,y,eq_top_of_torus_twisted_weyl hcard g hg _ ?_ ?_⟩
  · exact Subgroup.subset_closure (by simp [x])
  · exact Subgroup.subset_closure (by simp [y])

/-- Ordinary generation rank, before taking the central quotient. -/
theorem genRank_le_two (hcard : 4≤Nat.card F) :
    MarkedC4.genRank (SL2 (F:=F))≤2 := by
  obtain ⟨x,y,hxy⟩ := exists_generating_pair hcard
  have hc : Subgroup.closure (({x,y} : Finset (SL2 (F:=F))) : Set (SL2 (F:=F)))=⊤ := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

/-- The same two matrices, mapped through the actual central quotient,
generate the literal PSL₂ model. -/
theorem psl_exists_generating_pair (hcard : 4≤Nat.card F) :
    ∃ x y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      Subgroup.closure ({x,y} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))=⊤ := by
  obtain ⟨x,y,hxy⟩ := exists_generating_pair hcard
  let q := QuotientGroup.mk' (Subgroup.center (SL2 (F:=F)))
  refine ⟨q x,q y,?_⟩
  have he := congrArg (Subgroup.map q) hxy
  simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using he

theorem psl_genRank_le_two (hcard : 4≤Nat.card F) :
    MarkedC4.genRank (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)≤2 := by
  obtain ⟨x,y,hxy⟩ := psl_exists_generating_pair hcard
  have hc : Subgroup.closure
      (({x,y} : Finset (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))=⊤ := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGTypeASLTwoGeneration
