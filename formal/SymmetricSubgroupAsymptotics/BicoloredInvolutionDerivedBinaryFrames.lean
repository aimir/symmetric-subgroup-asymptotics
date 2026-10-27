import SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration
import SymmetricSubgroupAsymptotics.CFSGInvolutionDerivedEvenOrder

/-! Two elementary binary subgroups generate the ACTUAL derived group of
an involution system with two commuting colors and one isolated-edge
four-node configuration. No ambient node is assumed to lie in the derived
subgroup. The generators are literal even products in that subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BicoloredInvolutionDerivedBinaryFrames
open CFSGGeneration CFSGReduction CFSGCommutingBinaryFrameGeneration

/-- The extra two commuting vertices isolate one order-three edge. -/
theorem edge_product_mem {G : Type*} [Group G] (H : Subgroup G) (a b c d : G)
    (hc : c^2=1) (hd : d^2=1) (h3 : (a*b)^3=1)
    (hac : Commute a c) (hbd : Commute b d) (hcb : Commute c b)
    (hda : Commute d a) (hcd : Commute c d)
    (hu : a*c∈H) (hv : b*d∈H) : a*b∈H := by
  have hfactor : (a*c)*(b*d)=(a*b)*(c*d) := hcb.mul_mul_mul_comm a d
  have hcomm : Commute (a*b) (c*d) :=
    (hac.mul_left hcb.symm).mul_right (hda.symm.mul_left hbd)
  have hcd2 : (c*d)^2=1 := by rw [hcd.mul_pow,hc,hd,mul_one]
  have h2 : (a*b)^2∈H := by
    have hh := H.pow_mem (H.mul_mem hu hv) 2
    rw [hfactor,hcomm.mul_pow,hcd2,mul_one] at hh
    exact hh
  have hh := H.pow_mem h2 2
  have he : ((a*b)^2)^2=a*b := by
    rw [←pow_mul,show (2 : ℕ)*2=3+1 by decide,pow_succ,h3,one_mul]
  exact he ▸ hh

abbrev PairIndex {ι : Type*} (color : ι → Bool) (c : Bool) :=
  {p : ι×ι // color p.1=c ∧ color p.2=c}

/-- This is generation inside the original derived subgroup itself, not
normal generation and not generation of the ambient involution group. -/
theorem exists_binary_generating_subgroups {G : Type*} [Group G] {ι : Type*}
    (g : ι → G) (base : ι) (color : ι → Bool)
    (hgen : Subgroup.closure (Set.range g)=⊤)
    (hsq : ∀ i,g i*g i=1)
    (hsame : ∀ i,Abelianization.of (g i)=Abelianization.of (g base))
    (hcolor : ∀ i j,color i=color j → Commute (g i) (g j))
    (a b c d : ι)
    (ha : color a=false) (hb : color b=true)
    (hc : color c=false) (hd : color d=true)
    (hedge : (g a*g b)^3=1)
    (hcb : Commute (g c) (g b)) (hda : Commute (g d) (g a))
    (hcd : Commute (g c) (g d)) :
    ∃ U V : Subgroup (commutator G), IsPGroup 2 U ∧ IsPGroup 2 V ∧ U⊔V=⊤ := by
  let seed (s : Bool) (p : PairIndex color s) : commutator G :=
    derivedInvolutionProduct g base hsq hsame p.val.1 p.val.2
  have hframe (s : Bool) : Frame (seed s) := by
    refine ⟨1,?_,?_⟩
    · intro p
      apply Subtype.ext
      change (g p.val.1*g p.val.2)^(2^1)=1
      have hcomm := hcolor p.val.1 p.val.2 (p.property.1.trans p.property.2.symm)
      simpa only [pow_one] using
        (show (g p.val.1*g p.val.2)^2=1 by
          rw [hcomm.mul_pow,pow_two,pow_two,hsq,hsq,mul_one])
    · intro p q
      apply Subtype.ext
      change (g p.val.1*g p.val.2)*(g q.val.1*g q.val.2)=
        (g q.val.1*g q.val.2)*(g p.val.1*g p.val.2)
      exact (((hcolor _ _ (p.property.1.trans q.property.1.symm)).mul_right
        (hcolor _ _ (p.property.1.trans q.property.2.symm))).mul_left
        ((hcolor _ _ (p.property.2.trans q.property.1.symm)).mul_right
          (hcolor _ _ (p.property.2.trans q.property.2.symm)))).eq
  let U : Subgroup (commutator G) := Subgroup.closure (Set.range (seed false))
  let V : Subgroup (commutator G) := Subgroup.closure (Set.range (seed true))
  refine ⟨U,V,(hframe false).isPGroup,(hframe true).isPGroup,?_⟩
  let K : Subgroup (commutator G) := U⊔V
  let H : Subgroup G := K.map (commutator G).subtype
  have hwithin (i j : ι) (hij : color i=color j) : g i*g j∈H := by
    cases hi : color i with
    | false =>
      let p : PairIndex color false := ⟨(i,j),hi,hij.symm.trans hi⟩
      exact ⟨seed false p,Subgroup.mem_sup_left
        (Subgroup.subset_closure (Set.mem_range_self p)),rfl⟩
    | true =>
      let p : PairIndex color true := ⟨(i,j),hi,hij.symm.trans hi⟩
      exact ⟨seed true p,Subgroup.mem_sup_right
        (Subgroup.subset_closure (Set.mem_range_self p)),rfl⟩
  have hab : g a*g b∈H := edge_product_mem H (g a) (g b) (g c) (g d)
    (by simpa only [pow_two] using hsq c) (by simpa only [pow_two] using hsq d)
    hedge (hcolor a c (ha.trans hc.symm)) (hcolor b d (hb.trans hd.symm))
    hcb hda hcd (hwithin a c (ha.trans hc.symm)) (hwithin b d (hb.trans hd.symm))
  have hcross (i j : ι) (hi : color i=false) (hj : color j=true) : g i*g j∈H := by
    have hh := H.mul_mem (H.mul_mem (hwithin i a (hi.trans ha.symm)) hab)
      (hwithin b j (hb.trans hj.symm))
    have he : (g i*g a)*(g a*g b)*(g b*g j)=g i*g j := by
      calc
        _=g i*(g a*g a)*(g b*g b)*g j := by group
        _=g i*g j := by rw [hsq,hsq,mul_one,mul_one]
    exact he ▸ hh
  have hpairs (i j : ι) : g i*g j∈H := by
    cases hi : color i <;> cases hj : color j
    · exact hwithin i j (hi.trans hj.symm)
    · exact hcross i j hi hj
    · have hh := H.inv_mem (hcross j i hj hi)
      simpa only [mul_inv_rev,inv_eq_of_mul_eq_one_right (hsq i),
        inv_eq_of_mul_eq_one_right (hsq j)] using hh
    · exact hwithin i j (hi.trans hj.symm)
  have hDH : commutator G≤H := by
    rw [commutator_eq_involution_even_products g base hgen hsq hsame]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hpairs base i.val
  apply top_unique
  intro z _
  obtain ⟨w,hw,he⟩ := hDH z.property
  have hwz : w=z := Subtype.ext he
  exact hwz ▸ hw

end SymmetricSubgroupAsymptotics.BicoloredInvolutionDerivedBinaryFrames
