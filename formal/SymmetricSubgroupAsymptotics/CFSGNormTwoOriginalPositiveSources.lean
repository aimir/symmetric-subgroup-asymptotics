import SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootParents
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerPaths
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence

/-! ORIGINAL integral Serre source vectors attached to actual positive
norm-two roots. A nonsimple vector is DEFINED by the first divided power
along its selected smaller positive parent. Consequently its source parent
identity and its Cartan weights are proved without a matrix realization,
source-action certificate, spanning assertion, or faithfulness premise.
The recursion and all its proofs are uniform in E6/E7/E8 (and ADE). -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreLocalNilpotence
open CFSGSerreSignedRootWeights CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGIntegerHeightSign CFSGNormTwoPositiveRootParents
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

abbrev Positive := {k : Roots A // ∀i,0≤k.val i}

def rootHeight (k : Positive A) : ℕ := (height k.val.val).toNat

def IsSimple (k : Positive A) : Prop := ∃i,k.val=coordinateRoot A hd i

private def simpleNode (k : Positive A) (h : IsSimple A hd k) : Fin r :=
  Classical.choose h

private theorem simpleNode_spec (k : Positive A) (h : IsSimple A hd k) :
    k.val=coordinateRoot A hd (simpleNode A hd k h) := Classical.choose_spec h

structure Parent (k : Positive A) where
  node : Fin r
  root : Positive A
  coordinates : k.val.val=root.val.val+Pi.single node 1
  height_add_one : height root.val.val+1=height k.val.val
  pairing : integerPairing A root.val.val (Pi.single node 1)= -1

include hs hp in
private def parent (k : Positive A) (hn : ¬IsSimple A hd k) : Parent A k :=
  Classical.choice (by
    obtain ⟨i,p,hpos,he,hheight,_,hpair⟩ :=
      exists_parent A hd hs hp k.val k.property (fun i hi=>hn ⟨i,hi⟩)
    exact ⟨⟨i,⟨p,hpos⟩,he,hheight,hpair⟩⟩)

private theorem parent_rootHeight (k : Positive A) (hn : ¬IsSimple A hd k) :
    rootHeight A (parent A hd hs hp k hn).root+1=rootHeight A k := by
  have he := (parent A hd hs hp k hn).height_add_one
  have hp0 := height_pos A (parent A hd hs hp k hn).root.val
    (parent A hd hs hp k hn).root.property
  dsimp only [rootHeight]
  omega

include hd hs hp in
/-- Finite fuel is the actual coordinate height; zero fuel is unreachable
in the public source. It keeps the defining equations elementary. -/
private def sourceAux (neg : Bool) : ℕ→Positive A→integralLattice A
  | 0,_=>0
  | n+1,k=>if h : IsSimple A hd k then
      latticeGenerator A (if neg then .F (simpleNode A hd k h) else .E (simpleNode A hd k h))
    else integralOperator A neg (parent A hd hs hp k h).node 1
      (sourceAux neg n (parent A hd hs hp k h).root)

include hd hs hp in
def source (neg : Bool) (k : Positive A) : integralLattice A :=
  sourceAux A hd hs hp neg (rootHeight A k) k

/-- Coordinate Cartan weight, retaining the literal OLD Cartan matrix. -/
def weight (a : Fin r) (k : Positive A) : ℚ :=
  (integerPairing A (Pi.single a 1) k.val.val : ℚ)

private theorem weight_simple (a : Fin r) (k : Positive A) (h : IsSimple A hd k) :
    weight A a k=(A a (simpleNode A hd k h):ℚ) := by
  rw [weight,simpleNode_spec A hd k h]
  simp only [coordinateRoot,integerPairing,Matrix.toBilin'_single]

private theorem weight_parent (a : Fin r) (k : Positive A) (hn : ¬IsSimple A hd k) :
    (A a (parent A hd hs hp k hn).node:ℚ)+
      weight A a (parent A hd hs hp k hn).root=weight A a k := by
  change (A a (parent A hd hs hp k hn).node:ℚ)+
    (integerPairing A (Pi.single a 1) (parent A hd hs hp k hn).root.val.val:ℚ)=
      (integerPairing A (Pi.single a 1) k.val.val:ℚ)
  rw [(parent A hd hs hp k hn).coordinates,map_add,Int.cast_add]
  have he : integerPairing A (Pi.single a 1)
      (Pi.single (parent A hd hs hp k hn).node 1)=A a (parent A hd hs hp k hn).node := by
    simp only [integerPairing,Matrix.toBilin'_single]
  rw [he,add_comm]

private theorem sourceAux_weight (neg : Bool) (n : ℕ) (k : Positive A) (a : Fin r) :
    ⁅coroot A neg a,(sourceAux A hd hs hp neg n k).val⁆=
      weight A a k • (sourceAux A hd hs hp neg n k).val := by
  induction n generalizing k with
  | zero =>
    change ⁅coroot A neg a,(0 : RationalLie A)⁆=weight A a k • 0
    simp only [lie_zero,smul_zero]
  | succ n ih =>
    by_cases h : IsSimple A hd k
    · simp only [sourceAux,dif_pos h]
      have hw := coroot_root A neg a (simpleNode A hd k h)
      rw [←weight_simple A hd a k h] at hw
      cases neg <;> exact hw
    · simp only [sourceAux,dif_neg h]
      change ⁅coroot A neg a,dividedPower A neg (parent A hd hs hp k h).node 1
        (sourceAux A hd hs hp neg n (parent A hd hs hp k h).root).val⁆=_
      have hw := coroot_dividedPower A neg a (parent A hd hs hp k h).node _ _
        (ih (parent A hd hs hp k h).root) 1
      simpa only [Nat.cast_one,one_mul,weight_parent A hd hs hp a k h] using hw

theorem source_weight (neg : Bool) (k : Positive A) (a : Fin r) :
    ⁅coroot A neg a,(source A hd hs hp neg k).val⁆=
      weight A a k • (source A hd hs hp neg k).val :=
  sourceAux_weight A hd hs hp neg (rootHeight A k) k a

/-- The actual simple positive root, with its positivity proved literally. -/
def simpleRoot (i : Fin r) : Positive A :=
  ⟨coordinateRoot A hd i,by
    intro j
    change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num⟩

theorem source_simple (neg : Bool) (i : Fin r) :
    source A hd hs hp neg (simpleRoot A hd i)=
      latticeGenerator A (if neg then .F i else .E i) := by
  have h : IsSimple A hd (simpleRoot A hd i) := ⟨i,rfl⟩
  have hh : rootHeight A (simpleRoot A hd i)=1 := by
    change (height (Pi.single i (1:ℤ))).toNat=1
    rw [height_coordinate]
    rfl
  have hi : simpleNode A hd (simpleRoot A hd i) h=i := by
    apply coordinateRoot_injective A hd
    exact (simpleNode_spec A hd _ h).symm
  simp only [source,hh,sourceAux,dif_pos h,hi]

/-- Actual source-parent equality, not supplied as a source certificate.
The same chosen parent also has the required smaller height and weight. -/
theorem source_parent (neg : Bool) (k : Positive A) (hn : ¬IsSimple A hd k) :
    ∃ (i : Fin r) (p : Positive A),
      rootHeight A p+1=rootHeight A k ∧
      k.val.val=p.val.val+Pi.single i 1 ∧
      integerPairing A p.val.val (Pi.single i 1)= -1 ∧
      ⁅rootVector A neg i,(source A hd hs hp neg p).val⁆=
        (source A hd hs hp neg k).val := by
  let p := parent A hd hs hp k hn
  refine ⟨p.node,p.root,parent_rootHeight A hd hs hp k hn,p.coordinates,p.pairing,?_⟩
  have he : source A hd hs hp neg k=
      integralOperator A neg p.node 1 (source A hd hs hp neg p.root) := by
    conv_lhs => rw [source,←parent_rootHeight A hd hs hp k hn]
    simp only [sourceAux,dif_neg hn]
    rfl
  rw [he,integralOperator_one_coe_apply,LieAlgebra.ad_apply]

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources
