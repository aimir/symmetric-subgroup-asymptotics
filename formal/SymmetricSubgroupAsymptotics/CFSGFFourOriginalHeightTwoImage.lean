import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoSpan
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleImageCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSeparatingCartan
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The first seven positive source vectors have independent SAME
rational matrix images. Nonzero adjacent images follow by actual
opposite lowering to a simple generator. Distinct actual Cartan weights
then give independence without a cross-entry matrix table. This only
proves rational injectivity on this initial source span. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoImage
open CFSG.Models.Chevalley CFSGFFourSerreMatrices CFSGSerreSignedRootWeights
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightTwoSpan
open CFSGFFourOriginalSimpleImageCoordinates CFSGFFourOriginalSeparatingCartan
open CFSGSerreSimpleBracketLowering
open CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

theorem simple_image_ne_zero (j:Fin 4) : rationalRepresentation (generator A (.E j))≠0 := by
  intro hz
  have h:=congrArg (fun M:Mat=>coordinates M j) hz
  change coordinates (rationalRepresentation (generator A (.E j))) j=coordinates 0 j at h
  rw [coordinates_generator,map_zero,Pi.single_eq_same] at h
  exact one_ne_zero h

theorem adjacent_image_ne_zero (i j:Fin 4) (hij:i≠j) (ha:A i j≠0) :
    rationalRepresentation ⁅rootVector A false i,rootVector A false j⁆≠0 := by
  intro hz
  have hl:⁅oppositeVector A false i,⁅rootVector A false i,rootVector A false j⁆⁆=
      -(A i j:ℚ) • rootVector A false j := by
    simpa only [if_pos rfl,if_neg hij,add_zero] using opposite_simple_bracket A false i i j
  have h:=congrArg rationalRepresentation hl
  rw [LieHom.map_lie,hz,lie_zero,map_smul] at h
  have hc:-(A i j:ℚ)≠0:=neg_ne_zero.mpr (by exact_mod_cast ha)
  exact simple_image_ne_zero j ((smul_eq_zero.mp h.symm).resolve_left hc)

def initialRoot (j:Fin 7) : Fin 24:=⟨j.val,lt_trans j.isLt (by decide)⟩
def initialVectors (j:Fin 7) : L := (rootVectors false (initialRoot j)).val
def initialImages (j:Fin 7) : Mat := rationalRepresentation (initialVectors j)

theorem initial_image_ne_zero (j:Fin 7) : initialImages j≠0 := by
  fin_cases j
  · change rationalRepresentation (generator A (.E 3))≠0
    exact simple_image_ne_zero 3
  · change rationalRepresentation (generator A (.E 2))≠0
    exact simple_image_ne_zero 2
  · change rationalRepresentation (generator A (.E 1))≠0
    exact simple_image_ne_zero 1
  · change rationalRepresentation (generator A (.E 0))≠0
    exact simple_image_ne_zero 0
  · change rationalRepresentation ((rootVectors false 4).val)≠0
    rw [path_four]
    exact adjacent_image_ne_zero 3 2 (by decide) (by decide)
  · change rationalRepresentation ((rootVectors false 5).val)≠0
    rw [path_five]
    exact adjacent_image_ne_zero 2 1 (by decide) (by decide)
  · change rationalRepresentation ((rootVectors false 6).val)≠0
    rw [path_six]
    exact adjacent_image_ne_zero 1 0 (by decide) (by decide)

theorem initial_images_linearIndependent : LinearIndependent ℚ initialImages := by
  let D:Module.End ℚ Mat:=LieAlgebra.ad ℚ Mat (rationalRepresentation testCartan)
  have hi:Function.Injective (fun j:Fin 7=>(testWeight (initialRoot j):ℚ)) := by
    intro i j he
    have hz:testWeight (initialRoot i)=testWeight (initialRoot j):=Int.cast_injective he
    have hroot:=testWeight_injective hz
    exact Fin.ext (congrArg (fun k:Fin 24=>k.val) hroot)
  apply D.eigenvectors_linearIndependent' _ hi initialImages
  intro j
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change ⁅rationalRepresentation testCartan,initialImages j⁆=
      (testWeight (initialRoot j):ℚ) • initialImages j
    exact image_testCartan_weight (initialRoot j)
  · exact initial_image_ne_zero j

def initialSpace : Submodule ℚ L := Submodule.span ℚ (Set.range initialVectors)

theorem rationalRepresentation_injective_on_initialSpace :
    Set.InjOn rationalRepresentation (initialSpace:Set L) := by
  intro x hx y hy he
  change x∈Submodule.span ℚ (Set.range initialVectors) at hx
  change y∈Submodule.span ℚ (Set.range initialVectors) at hy
  obtain ⟨a,ha⟩:=(Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  obtain ⟨b,hb⟩:=(Submodule.mem_span_range_iff_exists_fun ℚ).mp hy
  have himage:(∑j:Fin 7,a j • initialImages j)=∑j:Fin 7,b j • initialImages j := by
    rw [←ha,←hb,map_sum,map_sum] at he
    simpa only [map_smul] using he
  have hab:a=b:=funext ((Fintype.linearIndependent_iffₛ.mp initial_images_linearIndependent) a b himage)
  rw [←ha,←hb,hab]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoImage
