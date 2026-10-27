import SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation
import SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration
import SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrixCertificates

/-! The selected four-involution certificate is transported back to the
original pinned presentation through its genuine injective representation.
The recovered original y word is retained explicitly. The generic helper
states its literal obligations; the final endpoint supplies them from
the separate seven-dimensional certificate leaf. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoOneBinaryFrameGoodSylow
open CFSGJankoOnePresentationGenerators CFSGJankoOneLiteralRepresentation
open CFSGCommutingBinaryFrameGeneration

def conjugator {G : Type} [Group G] (a b : G) : G := b*a*b*a*b^2
def secondInvolution {G : Type} [Group G] (a b : G) : G :=
  (conjugator a b)⁻¹*a*(conjugator a b)
def rotation {G : Type} [Group G] (a b : G) : G := a*secondInvolution a b
def seeds {G : Type} [Group G] (a b : G) : Fin 4 → G := fun i =>
  if i=0 then a else if i=1 then (rotation a b)^5 else
    if i=2 then b^2*a*b else b^2*((rotation a b)^5)*b
def recoveryIndices : List (Fin 4) := [2,1,2,0,3,1,2,1,0,2,0,3,0]

theorem map_rotation {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (rotation a b)=rotation (f a) (f b) := by
  simp only [rotation,secondInvolution,conjugator,map_mul,map_pow,map_inv]

theorem map_seed {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) (i : Fin 4) :
    f (seeds a b i)=seeds (f a) (f b) i := by
  unfold seeds
  split_ifs <;> simp only [map_mul,map_pow,map_rotation]

theorem goodSylowPrime_of_literal_guide {G : Type} [Group G]
    (hCFSG : CFSG.CFSGClassification) {x y : G}
    (hpacket : RelatorPacket x y) (hx : x≠1)
    (hrotation : (rotation x y)^10=1)
    (hrecovery : (recoveryIndices.map (seeds x y)).prod=y)
    [Finite CFSG.Models.Presentations.J1.Model]
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] :
    CFSGReduction.GoodSylowPrime CFSG.Models.Presentations.J1.Model 2 := by
  let a := pinnedX
  let b := pinnedY
  let t := secondInvolution a b
  let z := (rotation a b)^5
  have ha : a^2=1 := pinnedX_square
  have hb : b^3=1 := pinnedY_cube
  have hrot : (rotation a b)^10=1 := by
    apply representation_injective hpacket hx
    simpa only [a,b,map_pow,map_one,map_rotation,representation_pinnedX,representation_pinnedY]
      using hrotation
  have hrec : (recoveryIndices.map (seeds a b)).prod=b := by
    apply representation_injective hpacket hx
    simpa only [a,b,map_list_prod,List.map_map,Function.comp_def,map_seed,
      representation_pinnedX,representation_pinnedY] using hrecovery
  have ht : t^2=1 := by
    have haa : a*a=1 := by simpa only [pow_two] using ha
    change ((conjugator a b)⁻¹*a*(conjugator a b))^2=1
    rw [pow_two]
    calc
      _=(conjugator a b)⁻¹*(a*a)*(conjugator a b) := by group
      _=1 := by rw [haa]; simp only [mul_one,inv_mul_cancel]
  have Fu : Frame (pair a z) := halfProductFrame a t ha ht 5
    (by simpa only [show (2:ℕ)*5=10 by decide] using hrot)
  let v : Bool → CFSG.Models.Presentations.J1.Model := fun j => b⁻¹*pair a z j*b
  have Fv : Frame v := by
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
      Fu.map (MulAut.conj b⁻¹).toMonoidHom
  let P := Subgroup.closure (Set.range (pair a z))
  let Q := Subgroup.closure (Set.range v)
  have hbinv : b^2=b⁻¹ := eq_inv_of_mul_eq_one_left
    (by simpa only [pow_succ,pow_two] using hb)
  have hseed : ∀ i : Fin 4,seeds a b i∈P⊔Q := by
    intro i
    fin_cases i
    · change a∈P⊔Q
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨false,rfl⟩)
    · change z∈P⊔Q
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨true,rfl⟩)
    · change b^2*a*b∈P⊔Q
      rw [hbinv]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨false,rfl⟩)
    · change b^2*z*b∈P⊔Q
      rw [hbinv]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨true,rfl⟩)
  have hbjoin : b∈P⊔Q := by
    rw [←hrec]
    apply (P⊔Q).list_prod_mem
    intro g hg
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hg
    exact hseed i
  have hjoin : P⊔Q=⊤ := by
    apply top_unique
    rw [←presentation_pair_closure]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hga|hg
    · subst g
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨false,rfl⟩)
    · have hgb : g=b := Set.mem_singleton_iff.mp hg
      subst g
      exact hbjoin
  exact CFSGReduction.goodSylowTwo_of_two_binary_subgroups hCFSG P Q Fu.isPGroup Fv.isPGroup hjoin

theorem goodSylowPrime (hCFSG : CFSG.CFSGClassification)
    [Finite CFSG.Models.Presentations.J1.Model]
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] :
    CFSGReduction.GoodSylowPrime CFSG.Models.Presentations.J1.Model 2 := by
  apply goodSylowPrime_of_literal_guide hCFSG CFSGJankoOneSevenMatrices.relatorPacket
    CFSGJankoOneSevenMatrices.unitA_ne_one
  · simpa only [rotation,secondInvolution,conjugator,
      CFSGJankoOneSevenMatrices.rotation,CFSGJankoOneSevenMatrices.conjugator] using
      CFSGJankoOneSevenMatrices.rotation_tenth
  · have hs : seeds CFSGJankoOneSevenMatrices.unitA CFSGJankoOneSevenMatrices.unitB=
        CFSGJankoOneSevenMatrices.seeds := by
      funext i
      fin_cases i <;> simp [seeds,CFSGJankoOneSevenMatrices.seeds,rotation,
        secondInvolution,conjugator,CFSGJankoOneSevenMatrices.rotation,
        CFSGJankoOneSevenMatrices.conjugator]
    simpa only [hs,recoveryIndices,CFSGJankoOneSevenMatrices.recoveryIndices] using
      CFSGJankoOneSevenMatrices.recovery_product

end SymmetricSubgroupAsymptotics.CFSGJankoOneBinaryFrameGoodSylow
