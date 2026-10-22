import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairOrbit
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting

/-! General adjacent POSITIVE-root collecting on the original lattice
model. An actual simultaneous reflection descent reaches a simple/positive
pair. Original integer root-word comparison transports both parameters
and the sum root, so a single integer unit sign works in all characteristics.
No root-pair orbit or normalized commutator relation is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinatePositivePairOrbit CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateSignedRootCollecting CFSGNormTwoCoordinateRootCollectingTransport

private theorem mul_sign {a b : ℤ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a*b=1 ∨ a*b= -1 := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num

def sumRoot {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hs : A.transpose=A)
    (k l : Roots A) (hpair : integerPairing A k.val l.val= -1) : Roots A :=
  ⟨k.val+l.val,by
    rw [CFSGNormTwoPairingBounds.norm_add A hs,k.property,l.property,hpair] <;> norm_num⟩

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem positive_pair_commutator_sign (k l : Roots A)
    (hk : ∀t,0≤k.val t) (hl : ∀t,0≤l.val t)
    (hpair : integerPairing A k.val l.val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K] (a b : K),
      selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K l b*
        (selectedRootElement A hd hs hp ho K k a)⁻¹*(selectedRootElement A hd hs hp ho K l b)⁻¹=
      selectedRootElement A hd hs hp ho K (sumRoot A hs k l hpair) ((ε:K)*(a*b)) := by
  obtain ⟨w,j,hfirst,hsecond,hlj⟩ := exists_word_simple_positive_pair A hd hs hp ho k l hk hl hpair
  let l' := wordRoot A hs hp b₀ s₀ w l
  let g := sumRoot A hs k l hpair
  let g' := raisedRoot A hd hs hp ho l' j hlj
  have hg : wordRoot A hs hp b₀ s₀ w g=g' := by
    apply Subtype.ext
    calc
      _=wordLinear A hs hp b₀ s₀ w g.val := (wordLinear_root A hs hp b₀ s₀ w g).symm
      _=wordLinear A hs hp b₀ s₀ w k.val+wordLinear A hs hp b₀ s₀ w l.val := map_add _ _ _
      _=(s₀ j:Roots A).val+l'.val := by rw [wordLinear_root,wordLinear_root,hfirst]
      _=g'.val := by change (s₀ j:Roots A).val+l'.val=l'.val+(s₀ j:Roots A).val;abel
  obtain ⟨x,hx,hxword⟩ := word_selected_root_sign A hd hs hp ho w k
  rw [hfirst] at hxword
  obtain ⟨y,hy,hyword⟩ := word_selected_root_sign A hd hs hp ho w l
  obtain ⟨z,hz,hzword⟩ := word_selected_root_sign A hd hs hp ho w g
  obtain ⟨s,hsign,hsimple⟩ := selected_simple_root_sign A hd hs hp ho j
  obtain ⟨c,hc,hcollect⟩ := simple_positive_commutator_sign A hd hs hp ho l' hsecond j hlj
  let ε : ℤ := z*c*y*s*x
  have hε : ε=1 ∨ ε= -1 := mul_sign (mul_sign (mul_sign (mul_sign hz hc) hy) hsign) hx
  refine ⟨ε,hε,?_⟩
  intro K _ a b
  let φ : MulAut ((CoordMat A hd hs hp ho K)ˣ) := MulAut.conj (canonicalWord D K w)
  have hka : φ (selectedRootElement A hd hs hp ho K k a)=
      canonicalRoot D K false j ((s:K)*((x:K)*a)) :=
    (hxword K a).trans (hsimple K ((x:K)*a))
  have hlb : φ (selectedRootElement A hd hs hp ho K l b)=
      selectedRootElement A hd hs hp ho K l' ((y:K)*b) := hyword K b
  have himage : φ (selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K l b*
        (selectedRootElement A hd hs hp ho K k a)⁻¹*(selectedRootElement A hd hs hp ho K l b)⁻¹)=
      positiveRootCommutator A hd hs hp ho K l' j ((s:K)*((x:K)*a)) ((y:K)*b) := by
    simp only [map_mul,map_inv,hka,hlb,positiveRootCommutator]
  have hsum : φ (selectedRootElement A hd hs hp ho K g ((ε:K)*(a*b)))=
      selectedRootElement A hd hs hp ho K g' ((z:K)*((ε:K)*(a*b))) := by
    have hh := hzword K ((ε:K)*(a*b))
    rw [hg] at hh
    exact hh
  have hcoeff : (c:K)*(((y:K)*b)*((s:K)*((x:K)*a)))=(z:K)*((ε:K)*(a*b)) := by
    have hzz : (z:K)*(z:K)=1 := by rcases hz with rfl|rfl <;> norm_num
    dsimp only [ε]
    simp only [Int.cast_mul]
    calc
      _=((z:K)*(z:K))*((c:K)*(((y:K)*b)*((s:K)*((x:K)*a)))) := by rw [hzz,one_mul]
      _=_ := by ring
  apply φ.injective
  calc
    _=positiveRootCommutator A hd hs hp ho K l' j ((s:K)*((x:K)*a)) ((y:K)*b) := himage
    _=selectedRootElement A hd hs hp ho K g'
        ((c:K)*(((y:K)*b)*((s:K)*((x:K)*a)))) := hcollect K _ _
    _=selectedRootElement A hd hs hp ho K g' ((z:K)*((ε:K)*(a*b))) :=
      congrArg (selectedRootElement A hd hs hp ho K g') hcoeff
    _=_ := hsum.symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
