import SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleWeightSeparation
import SymmetricSubgroupAsymptotics.FiniteUnitScaledBasisCoordinates
import SymmetricSubgroupAsymptotics.FiniteLieWeightBasisSupport
import SymmetricSubgroupAsymptotics.FiniteLieFamilyCoefficientJacobi
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction
import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily

/-! Uniform ORIGINAL positive-half first-action stability from genuine
native root coordinates. Inputs are a universal source Lie map, an actual
full root/Cartan basis, its Cartan diagonal relation, and nonzero primitive
positive-source image scalars. No source action table, spanning, injective
source realization or exceptional recognition is assumed. The actual
raising/lowering coefficient rows are constructed from native brackets.
The parent row comes from the ORIGINAL source-parent relation; mixed rows
come from native Jacobi. This applies uniformly to ADE. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoNativePositiveSourceStability
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoOriginalPositiveSources CFSGNormTwoOriginalSourceInvolution
open CFSGNormTwoOriginalSourceBaseActions CFSGNormTwoSimpleWeightSeparation
open CFSGSerreSignedRootWeights CFSGSerreLocalNilpotence
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (phi : RationalLie A→ₗ⁅ℚ⁆L) (b : Module.Basis (Roots A⊕Fin r) ℚ L)
    (u : Positive A→ℚ)

private def embed : HalfIndex A↪(Roots A⊕Fin r) where
  toFun j:=match j with | .inl a=>.inr a | .inr k=>.inl k.val
  inj' j k h:=by
    cases j with
    | inl a =>
      cases k with
      | inl c =>
        change Sum.inr a=Sum.inr c at h
        exact congrArg Sum.inl (Sum.inr.inj h)
      | inr q => cases h
    | inr p =>
      cases k with
      | inl c => cases h
      | inr q =>
        change Sum.inl p.val=Sum.inl q.val at h
        exact congrArg Sum.inr (Subtype.ext (Sum.inl.inj h))

private def scale : HalfIndex A→ℚ
  | .inl _=>1
  | .inr k=>u k

def target (j : HalfIndex A) : L := phi (half A hd hs hp false j)

def coordinates : L→ₗ[ℚ](HalfIndex A→ℚ) :=
  FiniteUnitScaledBasisCoordinates.coordinates b (embed A) (scale A u)

def raising (i : Fin r) (j : HalfIndex A) : HalfIndex A→ℚ :=
  coordinates A b u ⁅phi (rootVector A false i),target A hd hs hp phi j⁆

def lowering (i : Fin r) (j : HalfIndex A) : HalfIndex A→ℚ :=
  coordinates A b u ⁅phi (oppositeVector A false i),target A hd hs hp phi j⁆

private def label : (Roots A⊕Fin r)→(Fin r→ℤ)
  | .inl k=>k.val
  | .inr _=>0

variable (hu : ∀k,u k≠0)
    (hH : ∀a,phi (generator A (.H a))=b (.inr a))
    (hroot : ∀k,phi (source A hd hs hp false k).val=u k • b (.inl k.val))
    (hdiag : ∀a j,⁅phi (generator A (.H a)),b j⁆=
      (integerPairing A (Pi.single a 1) (label A j):ℚ) • b j)

include hH hroot in
private theorem target_eq_scaled (j : HalfIndex A) :
    target A hd hs hp phi j=
      FiniteUnitScaledBasisCoordinates.vector b (embed A) (scale A u) j := by
  cases j with
  | inl a =>
    change phi (generator A (.H a))=1 • b (.inr a)
    rw [hH,one_smul]
  | inr k => exact hroot k

include hu in
private theorem scale_ne_zero (j : HalfIndex A) : scale A u j≠0 := by
  cases j with | inl _=>exact one_ne_zero | inr k=>exact hu k

include hu hH hroot in
/-- Exact actual coordinate left inverse on ORIGINAL source images. -/
theorem coordinates_target (j : HalfIndex A) :
    coordinates A b u (target A hd hs hp phi j)=Pi.single j 1 := by
  rw [target_eq_scaled A hd hs hp phi b u hH hroot]
  exact FiniteUnitScaledBasisCoordinates.coordinates_vector b (embed A) (scale A u)
    (scale_ne_zero A u hu) j

private theorem coordinates_nonzero (z : L) (j : HalfIndex A)
    (hj : coordinates A b u z j≠0) : b.repr z (embed A j)≠0 := by
  intro hz
  apply hj
  change (scale A u j)⁻¹*b.repr z (embed A j)=0
  rw [hz,mul_zero]

private theorem source_weight_image (a : Fin r) (j : HalfIndex A) :
    ⁅phi (generator A (.H a)),target A hd hs hp phi j⁆=
      halfWeight A a j • target A hd hs hp phi j := by
  have h:=congrArg (fun z=>phi z) (half_weight A hd hs hp false a j)
  simpa only [LieHom.map_lie,map_smul,coroot,Bool.false_eq_true,if_false] using h

private theorem acting_weight (neg : Bool) (a i : Fin r) :
    ⁅phi (generator A (.H a)),phi (rootVector A neg i)⁆=
      (if neg then -(A a i:ℚ) else (A a i:ℚ)) • phi (rootVector A neg i) := by
  cases neg
  · have h:=congrArg (fun z=>phi z) (coroot_root A false a i)
    simpa only [LieHom.map_lie,map_smul,coroot,Bool.false_eq_true,if_false] using h
  · have h:=congrArg (fun z=>phi z) (generator_HF A a i)
    simpa only [LieHom.map_lie,map_neg,map_zsmul,rootVector,if_true,
      Int.cast_smul_eq_zsmul,neg_smul] using h

private theorem bracket_weight (neg : Bool) (a i : Fin r) (j : HalfIndex A) :
    ⁅phi (generator A (.H a)),⁅phi (rootVector A neg i),target A hd hs hp phi j⁆⁆=
      ((if neg then -(A a i:ℚ) else (A a i:ℚ))+halfWeight A a j) •
        ⁅phi (rootVector A neg i),target A hd hs hp phi j⁆ := by
  rw [leibniz_lie,acting_weight,source_weight_image,smul_lie,lie_smul,add_smul]

include hdiag in
private theorem raised_label (i : Fin r) (k : Positive A) (j : Roots A⊕Fin r)
    (hj : b.repr ⁅phi (rootVector A false i),target A hd hs hp phi (.inr k)⁆ j≠0) :
    label A j=k.val.val+Pi.single i 1 := by
  apply label_eq_add_simple A hs hp
  intro a
  exact FiniteLieWeightBasisSupport.eigen_coordinate_support b
    (phi (generator A (.H a))) (fun j=>(integerPairing A (Pi.single a 1) (label A j):ℚ))
    (hdiag a) _ _ (bracket_weight A hd hs hp phi false a i (.inr k)) j hj

include hdiag in
private theorem lowered_label (i : Fin r) (k : Positive A) (j : Roots A⊕Fin r)
    (hj : b.repr ⁅phi (oppositeVector A false i),target A hd hs hp phi (.inr k)⁆ j≠0) :
    label A j=k.val.val-Pi.single i 1 := by
  apply label_eq_sub_simple A hs hp
  intro a
  exact FiniteLieWeightBasisSupport.eigen_coordinate_support b
    (phi (generator A (.H a))) (fun j=>(integerPairing A (Pi.single a 1) (label A j):ℚ))
    (hdiag a) _ _ (bracket_weight A hd hs hp phi true a i (.inr k)) j hj

include hu hH hroot in
private theorem reconstruct (z : L)
    (hz : z∈Submodule.span ℚ (Set.range (target A hd hs hp phi))) :
    Fintype.linearCombination ℚ (target A hd hs hp phi) (coordinates A b u z)=z := by
  have he : target A hd hs hp phi=
      FiniteUnitScaledBasisCoordinates.vector b (embed A) (scale A u) :=
    funext (target_eq_scaled A hd hs hp phi b u hH hroot)
  rw [he] at hz ⊢
  exact FiniteUnitScaledBasisCoordinates.reconstruction b (embed A) (scale A u)
    (scale_ne_zero A u hu) z hz

include hu hH hroot in
private theorem mem_span_of_support (z : L)
    (hz : ∀k,b.repr z k≠0→∃j,embed A j=k) :
    z∈Submodule.span ℚ (Set.range (target A hd hs hp phi)) := by
  have he : target A hd hs hp phi=
      FiniteUnitScaledBasisCoordinates.vector b (embed A) (scale A u) :=
    funext (target_eq_scaled A hd hs hp phi b u hH hroot)
  rw [he]
  exact FiniteUnitScaledBasisCoordinates.mem_span_of_support b (embed A) (scale A u)
    (scale_ne_zero A u hu) z hz

private theorem target_mem (j : HalfIndex A) :
    target A hd hs hp phi j∈Submodule.span ℚ (Set.range (target A hd hs hp phi)) :=
  Submodule.subset_span ⟨j,rfl⟩

include hu hH hroot hdiag in
private theorem target_raising (i : Fin r) (j : HalfIndex A) :
    ⁅phi (rootVector A false i),target A hd hs hp phi j⁆=
      Fintype.linearCombination ℚ (target A hd hs hp phi) (raising A hd hs hp phi b u i j) := by
  symm
  apply reconstruct A hd hs hp phi b u hu hH hroot
  cases j with
  | inl a =>
    have h:=congrArg (fun z=>phi z) (raising_cartan A hd hs hp false i a)
    change phi ⁅rootVector A false i,half A hd hs hp false (.inl a)⁆=
      phi ((-(A a i:ℚ)) • half A hd hs hp false (.inr (simpleRoot A hd i))) at h
    rw [LieHom.map_lie,map_smul] at h
    change ⁅phi (rootVector A false i),target A hd hs hp phi (.inl a)⁆=
      (-(A a i:ℚ)) • target A hd hs hp phi (.inr (simpleRoot A hd i)) at h
    rw [h]
    exact Submodule.smul_mem _ _ (target_mem A hd hs hp phi _)
  | inr k =>
    apply mem_span_of_support A hd hs hp phi b u hu hH hroot
    intro q hq
    cases q with
    | inl q =>
      have he:=raised_label A hd hs hp phi b hdiag i k (.inl q) hq
      change q.val=k.val.val+Pi.single i 1 at he
      have hpos : ∀a,0≤q.val a := by rw [he];exact raised_nonnegative A i k
      exact ⟨.inr ⟨q,hpos⟩,rfl⟩
    | inr a => exact ⟨.inl a,rfl⟩

include ho hu hH hroot hdiag in
private theorem target_lowering (i : Fin r) (j : HalfIndex A)
    (hj : 0<halfHeight A j) :
    ⁅phi (oppositeVector A false i),target A hd hs hp phi j⁆=
      Fintype.linearCombination ℚ (target A hd hs hp phi) (lowering A hd hs hp phi b u i j) := by
  symm
  apply reconstruct A hd hs hp phi b u hu hH hroot
  cases j with
  | inl a => change 0<0 at hj;omega
  | inr k =>
    by_cases hk : rootHeight A k=1
    · obtain ⟨a,_,hrow⟩:=lowering_height_one A hd hs hp false i k hk
      change ⁅oppositeVector A false i,(source A hd hs hp false k).val⁆=
        if i=a then -coroot A false i else 0 at hrow
      change ⁅phi (oppositeVector A false i),phi (source A hd hs hp false k).val⁆∈_
      rw [←LieHom.map_lie,hrow]
      split_ifs
      · rw [map_neg]
        exact Submodule.neg_mem _ (target_mem A hd hs hp phi (.inl i))
      · rw [map_zero];exact Submodule.zero_mem _
    · have hk' : 1<rootHeight A k := by change 0<rootHeight A k at hj;omega
      apply mem_span_of_support A hd hs hp phi b u hu hH hroot
      intro q hq
      cases q with
      | inl q =>
        have he:=lowered_label A hd hs hp phi b hdiag i k (.inl q) hq
        have hpos:=lowered_root_nonnegative A hd hs hp ho i k hk' q he
        exact ⟨.inr ⟨q,hpos⟩,rfl⟩
      | inr a => exact ⟨.inl a,rfl⟩

/-- ORIGINAL source reconstruction on its own positive-half span. The
coordinate left inverse suffices; source-map injectivity is not assumed. -/
private theorem source_reconstruct (z : RationalLie A)
    (hc : ∀j,coordinates A b u (target A hd hs hp phi j)=Pi.single j 1)
    (hz : z∈Submodule.span ℚ (Set.range (half A hd hs hp false))) :
    Fintype.linearCombination ℚ (half A hd hs hp false) (coordinates A b u (phi z))=z := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro z hz
    obtain ⟨j,rfl⟩:=hz
    rw [show phi (half A hd hs hp false j)=target A hd hs hp phi j from rfl,hc]
    simp [Fintype.linearCombination_apply,Pi.single_apply]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    rw [map_add,map_add,map_add,hx,hy]
  · intro q x _ hx
    rw [map_smul,map_smul,map_smul,hx]

private theorem source_cartan_raise_mem (i a : Fin r) :
    ⁅rootVector A false i,half A hd hs hp false (.inl a)⁆∈
      Submodule.span ℚ (Set.range (half A hd hs hp false)) := by
  rw [raising_cartan A hd hs hp false i a]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)

private theorem source_simple_lower_mem (i : Fin r) (k : Positive A)
    (hk : rootHeight A k=1) :
    ⁅oppositeVector A false i,half A hd hs hp false (.inr k)⁆∈
      Submodule.span ℚ (Set.range (half A hd hs hp false)) := by
  obtain ⟨a,_,hrow⟩:=lowering_height_one A hd hs hp false i k hk
  change ⁅oppositeVector A false i,(source A hd hs hp false k).val⁆∈_
  rw [hrow]
  split_ifs
  · exact Submodule.neg_mem _ (Submodule.subset_span ⟨.inl i,rfl⟩)
  · exact Submodule.zero_mem _

include hdiag in
private theorem raising_height (i : Fin r) (j : HalfIndex A)
    (hj : 0<halfHeight A j) (l : HalfIndex A)
    (hl : raising A hd hs hp phi b u i j l≠0) :
    halfHeight A l=halfHeight A j+1 := by
  cases j with
  | inl a => change 0<0 at hj;omega
  | inr k =>
    have hn:=coordinates_nonzero A b u _ l hl
    have he:=raised_label A hd hs hp phi b hdiag i k (embed A l) hn
    cases l with
    | inl a =>
      have he':=congrFun he i
      change 0=k.val.val i+(Pi.single i (1:ℤ) : Fin r→ℤ) i at he'
      simp only [Pi.single_eq_same] at he'
      have hk:=k.property i
      omega
    | inr q => exact raised_height A i k q he

include hdiag in
private theorem lowering_height (i : Fin r) (j : HalfIndex A)
    (hj : 0<halfHeight A j) (l : HalfIndex A)
    (hl : lowering A hd hs hp phi b u i j l≠0) :
    halfHeight A l+1=halfHeight A j := by
  cases j with
  | inl a => change 0<0 at hj;omega
  | inr k =>
    have hn:=coordinates_nonzero A b u _ l hl
    have he:=lowered_label A hd hs hp phi b hdiag i k (embed A l) hn
    cases l with
    | inl a =>
      change (0:Fin r→ℤ)=k.val.val-Pi.single i 1 at he
      have hv : k.val.val=Pi.single i 1 := sub_eq_zero.mp he.symm
      have hh : rootHeight A k=1 := by
        change (∑a,k.val.val a).toNat=1
        simp [hv]
      change 0+1=rootHeight A k
      omega
    | inr q => exact lowered_height A i k q he

private theorem embedded_weight (a : Fin r) (j : HalfIndex A) :
    (integerPairing A (Pi.single a 1) (label A (embed A j)):ℚ)=halfWeight A a j := by
  cases j with
  | inl i => simp only [embed,label,halfWeight,map_zero,Int.cast_zero]
  | inr k => rfl

include hdiag in
private theorem raising_weight_support (i a : Fin r) (j l : HalfIndex A)
    (hl : raising A hd hs hp phi b u i j l≠0) :
    halfWeight A a l=(A a i:ℚ)+halfWeight A a j := by
  have hn:=coordinates_nonzero A b u _ l hl
  have he:=FiniteLieWeightBasisSupport.eigen_coordinate_support b
    (phi (generator A (.H a))) (fun j=>(integerPairing A (Pi.single a 1) (label A j):ℚ))
    (hdiag a) _ _ (bracket_weight A hd hs hp phi false a i j) (embed A l) hn
  change (integerPairing A (Pi.single a 1) (label A (embed A l)):ℚ)=
    (A a i:ℚ)+halfWeight A a j at he
  rw [embedded_weight] at he
  exact he

include hu hH hroot ho hdiag in
/-- Every first action on the ACTUAL ORIGINAL positive source half is
proved from the native basis and Serre relations. The coefficient rows
are actual native brackets, not additional source-table hypotheses. -/
theorem positive_source_tables :
    (∀i j,⁅rootVector A false i,half A hd hs hp false j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp false)
        (raising A hd hs hp phi b u i j)) ∧
    (∀i j,0<halfHeight A j→⁅oppositeVector A false i,half A hd hs hp false j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp false)
        (lowering A hd hs hp phi b u i j)) := by
  have hc:=coordinates_target A hd hs hp phi b u hu hH hroot
  have hE:=target_raising A hd hs hp phi b u hu hH hroot hdiag
  have hF:=target_lowering A hd hs hp ho phi b u hu hH hroot hdiag
  apply CFSGSerreFiniteRootFamilyInduction.source_tables A (half A hd hs hp false)
    false (halfHeight A) (halfWeight A)
    (raising A hd hs hp phi b u) (lowering A hd hs hp phi b u) hd
    (half_weight A hd hs hp false)
  · intro i j hj
    cases j with
    | inl a =>
      have h:=source_reconstruct A hd hs hp phi b u _ hc
        (source_cartan_raise_mem A hd hs hp i a)
      simpa only [raising,LieHom.map_lie,target] using h.symm
    | inr k =>
      have hp':=rootHeight_pos A k
      change rootHeight A k=0 at hj
      omega
  · intro i j hj
    cases j with
    | inl a => change 0=1 at hj;omega
    | inr k =>
      have h:=source_reconstruct A hd hs hp phi b u _ hc
        (source_simple_lower_mem A hd hs hp i k hj)
      simpa only [lowering,LieHom.map_lie,target] using h.symm
  · exact lowering_height A hd hs hp phi b u hdiag
  · exact raising_height A hd hs hp phi b u hdiag
  · intro i a j hj l hl
    exact raising_weight_support A hd hs hp phi b u hdiag i a j l hl
  · intro i j hj
    cases j with
    | inl a => change 0<0 at hj;omega
    | inr k => exact CFSGNormTwoOriginalSourceFamily.positive_comparison A hs hp i k
  · intro j hj
    cases j with
    | inl a => change 1<0 at hj;omega
    | inr k =>
      have hn : ¬IsSimple A hd k := by
        rintro ⟨a,ha⟩
        have hv : k.val.val=Pi.single a 1 := congrArg Subtype.val ha
        have hh : rootHeight A k=1 := by
          change (∑i,k.val.val i).toNat=1
          simp [hv]
        change 1<rootHeight A k at hj
        omega
      obtain ⟨i,p,hh,_,_,hpath⟩:=source_parent A hd hs hp false k hn
      have hnative : ⁅phi (rootVector A false i),target A hd hs hp phi (.inr p)⁆=
          target A hd hs hp phi (.inr k) := by
        simpa only [target,LieHom.map_lie] using congrArg (fun z=>phi z) hpath
      refine ⟨i,.inr p,1,one_ne_zero,rootHeight_pos A p,hh,?_,?_⟩
      · simpa only [half,one_smul] using hpath
      · change coordinates A b u ⁅phi (rootVector A false i),target A hd hs hp phi (.inr p)⁆=
          (1:ℚ) • Pi.single (.inr k) 1
        rw [hnative,hc,one_smul]
  · intro i a j hj
    have hEF : ∀a i,⁅phi (oppositeVector A false a),phi (rootVector A false i)⁆=
        if a=i then -phi (generator A (.H a)) else 0 := by
      intro a i
      by_cases h:a=i
      · subst i
        rw [if_pos rfl,←LieHom.map_lie,opposite_same,map_neg]
        rfl
      · rw [if_neg h,←LieHom.map_lie,opposite_distinct A false a i h,map_zero]
    exact FiniteLieFamilyCoefficientJacobi.mixed_coefficients
      (target A hd hs hp phi) (coordinates A b u) hc
      (fun i=>phi (rootVector A false i)) (fun a=>phi (oppositeVector A false a))
      (fun a=>phi (generator A (.H a)))
      (raising A hd hs hp phi b u) (lowering A hd hs hp phi b u) (halfWeight A)
      hE hEF (source_weight_image A hd hs hp phi) i a j (hF a j hj)
      (fun l hl=>hF a l (by
        have hh:=raising_height A hd hs hp phi b u hdiag i j hj l hl
        omega))

include hu hH hroot ho hdiag in
/-- The checked source involution transports the SAME coefficient rows
to the negative half; no second exceptional root table is introduced. -/
theorem signed_source_tables (neg : Bool) :
    (∀i j,⁅rootVector A neg i,half A hd hs hp neg j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp neg)
        (raising A hd hs hp phi b u i j)) ∧
    (∀i j,0<halfHeight A j→⁅oppositeVector A neg i,half A hd hs hp neg j⁆=
      Fintype.linearCombination ℚ (half A hd hs hp neg)
        (lowering A hd hs hp phi b u i j)) := by
  have h:=positive_source_tables A hd hs hp ho phi b u hu hH hroot hdiag
  cases neg
  · exact h
  · constructor
    · intro i j
      exact action_identity_transport A hd hs hp false false i j _ (h.1 i j)
    · intro i j hj
      exact action_identity_transport A hd hs hp true false i j _ (h.2 i j hj)

end SymmetricSubgroupAsymptotics.CFSGNormTwoNativePositiveSourceStability
