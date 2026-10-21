import SymmetricSubgroupAsymptotics.CFSGAlternatingStarAutomorphismExt

/-! Actual point recognition of automorphisms preserving single
3-cycles. The argument applies in degrees five and six as well. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleRecognition
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleGeometry
open CFSGAlternatingThreeCycleStars CFSGAlternatingStarRelations
open CFSGAlternatingStarReconstruction CFSGAlternatingStarAutomorphismExt
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Preserving the single 3-cycles forces an automorphism to arise from
one actual permutation of the original points. Four distinguished
points suffice; no special low-degree classification is used. -/
theorem exists_permutation_conjugation (a b c d : α) (hfour : [a,b,c,d].Nodup)
    (f : MulAut (alternatingGroup α))
    (hpres : ∀ g : alternatingGroup α,g.val.IsThreeCycle→(f g).val.IsThreeCycle) :
    ∃ σ : Perm α,f=(MulAut.conjNormal : Perm α→*MulAut (alternatingGroup α)) σ := by
  have hab : a≠b := by grind
  let s : α→alternatingGroup α := fun i =>
    if hi : i≠a ∧ i≠b then
      ⟨cycle a b i,(cycle_isThreeCycle a b i hab (Ne.symm hi.1) (Ne.symm hi.2)).mem_alternatingGroup⟩
    else ⟨cycle a b c,(cycle_isThreeCycle a b c hab (by grind) (by grind)).mem_alternatingGroup⟩
  have hs : ∀ i,i≠a→i≠b→(s i).val=cycle a b i := by
    intro i hia hib
    simp only [s,dif_pos (And.intro hia hib)]
  let F : α→Perm α := fun i => (f (s i)).val
  have hF : ∀ i,i≠a→i≠b→(F i).IsThreeCycle := by
    intro i hia hib
    apply hpres
    rw [hs i hia hib]
    exact cycle_isThreeCycle a b i hab (Ne.symm hia) (Ne.symm hib)
  have hrel : ∀ i j,[a,b,i,j].Nodup→(F i*F j)^2=1 ∧ F i*F j≠1 := by
    intro i j hij
    have hia : i≠a := by grind
    have hib : i≠b := by grind
    have hja : j≠a := by grind
    have hjb : j≠b := by grind
    have hp : (s i*s j)^2=1 := by
      apply Subtype.ext
      change ((s i).val*(s j).val)^2=1
      rw [hs i hia hib,hs j hja hjb]
      exact product_square a b i j hij
    constructor
    · have hm := congrArg (fun x : alternatingGroup α => (f x).val) hp
      simpa only [map_pow,map_mul,map_one,F] using hm
    · intro he
      have hm : f (s i*s j)=f 1 := by
        apply Subtype.ext
        simpa only [map_mul,map_one,F] using he
      have hm' := congrArg (fun x : alternatingGroup α => x.val) (f.injective hm)
      change (s i).val*(s j).val=1 at hm'
      rw [hs i hia hib,hs j hja hjb] at hm'
      exact product_ne_one a b i j hij hm'
  obtain ⟨A,B,C,D,hABCD,hp,hq⟩ := pair_normal_form (F c) (F d)
    (hF c (by grind) (by grind)) (hF d (by grind) (by grind))
    (hrel c d hfour).1 (hrel c d hfour).2
  have hform : ∀ i,i≠a→i≠b→∃ e,e≠A ∧ e≠B ∧ F i=cycle A B e := by
    intro i hia hib
    by_cases hic : i=c
    · subst i
      exact ⟨C,by grind,by grind,hp⟩
    by_cases hid : i=d
    · subst i
      exact ⟨D,by grind,by grind,hq⟩
    have hc := hrel c i (by grind)
    have hd := hrel d i (by grind)
    rw [hp] at hc
    rw [hq] at hd
    obtain ⟨e,he,hre⟩ := third_normal_form A B C D hABCD (F i) (hF i hia hib)
      hc.1 hc.2 hd.1
    exact ⟨e,by grind,by grind,hre⟩
  have hinj : ∀ i j,i≠a→i≠b→j≠a→j≠b→F i=F j→i=j := by
    intro i j hia hib hja hjb he
    have hf : f (s i)=f (s j) := Subtype.ext he
    have hh := congrArg (fun g : alternatingGroup α => g.val b) (f.injective hf)
    change (s i : Perm α) b=(s j : Perm α) b at hh
    rw [hs i hia hib,hs j hja hjb] at hh
    simp only [cycle,Perm.mul_apply,swap_apply_def] at hh
    grind
  obtain ⟨σ,hσa,hσb,hσ⟩ := exists_point_conjugator a b A B hab (by grind) F hform hinj
  refine ⟨σ,?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext_of_star _ _ a b hab
  intro i hia hib
  apply Subtype.ext
  change (f ⟨cycle a b i,_⟩).val=σ*cycle a b i*σ⁻¹
  have he : s i=⟨cycle a b i,
    (cycle_isThreeCycle a b i hab (Ne.symm hia) (Ne.symm hib)).mem_alternatingGroup⟩ :=
    Subtype.ext (hs i hia hib)
  simpa only [F,he] using hσ i hia hib

end SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleRecognition
