import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleGauss
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylRootDichotomy
import SymmetricSubgroupAsymptotics.CFSGSimpleBruhatMultiplication
import SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatSquareCover

/-! Actual word-indexed Bruhat coverage of the WHOLE original G2 Model
in finite characteristic three. Every local complement, Gauss and root
alternative is proved for the literal root words. Finite Weyl-word
reduction and cell uniqueness are separate later obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWordBruhatCover
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoOriginalBorel CFSGGTwoOriginalSimpleGauss
open CFSGGTwoPositiveWordSubgroup CFSGGTwoPositiveCoordinateKernels
open CFSGGTwoSimpleBruhatComplement CFSGGTwoSimpleWeylNegative
open CFSGGTwoOriginalWeylRootDichotomy CFSGWeylWordBruhatCover
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

theorem word_torus_normalizer (w : List (Fin 2)) :
    wordValue (simpleWeyl K) w∈Subgroup.normalizer (torus K:Set (Model A K)) := by
  induction w with
  | nil => exact (Subgroup.normalizer (torus K:Set (Model A K))).one_mem
  | cons i w ih =>
      exact (Subgroup.normalizer (torus K:Set (Model A K))).mul_mem
        (simple_torus_normalizer K i) ih

theorem word_inverse_conj_torus (w : List (Fin 2)) (t : Model A K) (ht : t∈torus K) :
    (wordValue (simpleWeyl K) w)⁻¹*t*wordValue (simpleWeyl K) w∈torus K := by
  have hn := (Subgroup.normalizer (torus K:Set (Model A K))).inv_mem (word_torus_normalizer K w)
  have he := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  simpa only [inv_inv] using he

theorem local_word_step (i : Fin 2) (w : List (Fin 2)) (b : Model A K)
    (hb : b∈borel K) :
    WordCells (borel K) (simpleWeyl K)
      (simpleWeyl K i*b*wordValue (simpleWeyl K) w) := by
  have he := CFSGSimpleBruhatMultiplication.left_simple_cell
    (borel K) (positiveWordGroup K) (torus K) (complement K i)
    (simpleWeyl K i) (wordValue (simpleWeyl K) w) b
    (positiveModel K (simpleIndex i)) (modelRoot A K true i)
    (positive_le_borel K) (torus_le_borel K) (simple_factor K i b hb)
    (fun v hv=>positive_le_borel K (complement_positive K i v hv))
    (word_inverse_conj_torus K w) (word_simple_root_dichotomy K w i)
    (positiveModel_zero K (simpleIndex i)) (simple_gauss K i)
  rcases he with he|he
  · exact ⟨i::w,he⟩
  · exact ⟨w,he⟩

omit [Finite K] [CharP K 3] in
private theorem simple_negative (i : Fin 2) (t : K) :
    simpleWeyl K i*positiveModel K (simpleIndex i) (-t)*(simpleWeyl K i)⁻¹=
      modelRoot A K true i t := by
  fin_cases i
  · simpa only [neg_neg] using short_original K (-t)
  · simpa only [neg_neg] using long_original K (-t)

theorem borel_weyl_generate :
    Subgroup.closure ((borel K:Set (Model A K))∪Set.range (simpleWeyl K))=⊤ := by
  let H : Subgroup (Model A K) :=
    Subgroup.closure ((borel K:Set (Model A K))∪Set.range (simpleWeyl K))
  change H=⊤
  apply top_unique
  rw [←rootSet_generate A K]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg,i,t,rfl⟩
  have hpos (t : K) : positiveModel K (simpleIndex i) t∈H :=
    Subgroup.subset_closure (Or.inl
      (positive_le_borel K (positiveElement K (simpleIndex i) t).property))
  cases neg
  · have hh := hpos t
    have hp : positiveModel K (simpleIndex i) t=modelRoot A K false i t := by
      fin_cases i <;> simp [positiveModel,simpleIndex,directionModel,
        CFSGGTwoPositiveDirections.rootNode]
    exact hp ▸ hh
  · have hs : simpleWeyl K i∈H := Subgroup.subset_closure (Or.inr ⟨i,rfl⟩)
    rw [←simple_negative K i t]
    exact H.mul_mem (H.mul_mem hs (hpos (-t))) (H.inv_mem hs)

theorem original_word_bruhat (g : Model A K) :
    WordCells (borel K) (simpleWeyl K) g := by
  apply CFSGWeylWordBruhatSquareCover.closure_le_wordCells
    (borel K) (simpleWeyl K) (simple_square_mem_borel K) (local_word_step K) g
  rw [borel_weyl_generate]
  exact Subgroup.mem_top g

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWordBruhatCover
