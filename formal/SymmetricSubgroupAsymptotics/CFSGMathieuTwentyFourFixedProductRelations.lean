import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSharedSwapChart
import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding

/-! Seven exact pinned M24 relators, necessary on the actual image of x
under an automorphism fixing a=x*y. Recovered y is u^-1*a. No converse,
automorphism extension or accepted-capacity premise is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFixedProductRelations
open CFSGMathieuTwentyFourPresentationWords
open CFSGMathieuTwentyFourGoodSylowTwentyThree
open CFSGMathieuTwentyFourActualRepresentation
open CFSGMathieuTwentyFourSwapFibreOuterReduction
open CFSGMathieuTwentyFourSharedSwapChart
open CFSGMathieuTwentyFourTailDecodeTransport
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEvaluation.Letter

def relationValue {G : Type*} [Group G] (r : Fin 7) (a u : G) : G :=
  let w := u⁻¹*a
  match r.val with
  | 0 => u^2
  | 1 => w^3
  | 2 => (u*w)^23
  | 3 => (CFSG.Models.commWord u w)^12
  | 4 => (CFSG.Models.commWord u (w*u*w))^5
  | 5 => sixthWord u w
  | _ => seventhWord u w

theorem relationValue_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (r : Fin 7) (a u : G) :
    f (relationValue r a u)=relationValue r (f a) (f u) := by
  fin_cases r <;> simp only [relationValue,CFSG.Models.commWord,sixthWord,seventhWord,
    map_pow,map_mul,map_inv]

theorem original_pair_relations (r : Fin 7) : relationValue r (x*y) x=1 := by
  fin_cases r
  · simpa only [relationValue] using relator_zero
  · simpa only [relationValue,inv_mul_cancel_left] using relator_one
  · simpa only [relationValue,inv_mul_cancel_left] using relator_two
  · simpa only [relationValue,inv_mul_cancel_left] using relator_three
  · simpa only [relationValue,inv_mul_cancel_left] using relator_four
  · simpa only [relationValue,inv_mul_cancel_left] using relator_five
  · simpa only [relationValue,inv_mul_cancel_left] using relator_six

theorem pinned_pair_relations [IsSimpleGroup CFSG.Models.Presentations.M24.Model]
    (r : Fin 7) : relationValue r product pinnedX=1 := by
  apply permutationRepresentation_injective
  rw [relationValue_map,map_one]
  have hx : permutationRepresentation pinnedX=x.val :=
    permutationRepresentation_of_zero.trans x_coe_eq.symm
  have hy : permutationRepresentation pinnedY=y.val :=
    permutationRepresentation_of_one.trans y_coe_eq.symm
  rw [product,map_mul,hx,hy]
  exact (relationValue_map CFSG.Certificates.Mathieu24.M24Subgroup.subtype r (x*y) x).symm.trans
    (by rw [original_pair_relations]; rfl)

theorem fixed_image_relations [IsSimpleGroup CFSG.Models.Presentations.M24.Model]
    (f : OuterFixedElementEvaluationBound.fixedAutomorphisms product) (r : Fin 7) :
    relationValue r (permutationRepresentation product)
      (permutationRepresentation (f.val pinnedX))=1 := by
  have hf : f.val product=product := f.property
  have hh := congrArg f.val (pinned_pair_relations r)
  change f.val.toMonoidHom (relationValue r product pinnedX)=_ at hh
  rw [relationValue_map] at hh
  change relationValue r (f.val product) (f.val pinnedX) = f.val 1 at hh
  rw [hf,map_one] at hh
  have hm := congrArg permutationRepresentation hh
  rw [relationValue_map,map_one] at hm
  exact hm

def yWord : List Letter := [secondInv,first]
def commXY : List Letter := [secondInv] ++ inverseWord yWord ++ [second] ++ yWord

def relationWord (r : Fin 7) : List Letter :=
  match r.val with
  | 0 => powerWord [second] 2
  | 1 => powerWord yWord 3
  | 2 => powerWord ([second]++yWord) 23
  | 3 => powerWord commXY 12
  | 4 => let z := yWord++[second]++yWord
         powerWord ([secondInv]++inverseWord z++[second]++z) 5
  | 5 => powerWord ([second]++yWord++[second]++yWord++[second]++inverseWord yWord) 3 ++
         powerWord ([second]++yWord++[second]++inverseWord yWord++[second]++inverseWord yWord) 3
  | _ => powerWord ([second]++yWord++powerWord
           ([second]++yWord++[second]++inverseWord yWord) 3) 4

theorem eval_relationWord {G : Type*} [Group G] (r : Fin 7) (a u : G) :
    eval a u (relationWord r)=relationValue r a u := by
  fin_cases r <;> simp only [relationWord,yWord,commXY,eval_power,eval_append,eval_inverse,
    eval,value,mul_one,relationValue,CFSG.Models.commWord,sixthWord,seventhWord,mul_assoc]

def Accepts (c : Code22) : Prop := ∀ r : Fin 7,
  relationValue r (permutationRepresentation product) (sharedSwapDecode c)=1

theorem swapFibre_has_accepting_code [IsSimpleGroup CFSG.Models.Presentations.M24.Model]
    (f : SwapFibre) : ∃ c : Code22,
      sharedSwapDecode c=permutationRepresentation (f.val.val pinnedX) ∧ Accepts c := by
  obtain ⟨c,hc⟩ := swapFibre_image_has_shared_code f
  refine ⟨c,hc,?_⟩
  intro r
  rw [hc]
  exact fixed_image_relations f.val r

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFixedProductRelations
