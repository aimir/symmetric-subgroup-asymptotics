import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerCommutators
import Mathlib.Data.Fintype.Perm

/-! With zero actual odd kernel, the actual top kernel is elementary
binary. A cubic local block stabilizer forces its local projection zero;
this records the genuine obstruction before choosing a V4 section. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddTopKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)

local instance : Fintype (Equiv.Perm (Fin 3)) := fintypePerm
local instance : DecidableEq (Equiv.Perm (Fin 3)) := Fintype.decidableEqEquivFintype

private theorem cubic_kills_commuting_involution : ∀ p q : Equiv.Perm (Fin 3),
    p^2=1 → q^3=1 → q≠1 → p*(q*p*q⁻¹)=(q*p*q⁻¹)*p → p=1 := by
  decide +kernel

variable (C : Subgroup Frame) (hzero : oddKernel C=⊥)

private theorem sign_square (g : Sign (R := Equiv.Perm (Fin 4)) (I := Fin 4))
    (ht : g.right=1) : g^2=1 := by
  apply SemidirectProduct.ext
  · have hs : g.left*g.left=1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      exact binary_add_self _
    simpa [pow_two,SemidirectProduct.mul_left,ht] using hs
  · change g.right*g.right=1
    rw [ht,one_mul]

include hzero in
/-- The sign kernel being zero kills actual top-kernel squares. -/
theorem square (x : (top C).ker) : x^2=1 := by
  have ht : (signProjection C (x : C)).right=1 := x.property
  have hs := sign_square (signProjection C (x : C)) ht
  have hm : (x : C)^2∈oddKernel C := by
    change signProjection C ((x : C)^2)=1
    rw [map_pow,hs]
  apply Subtype.ext
  exact Subgroup.mem_bot.mp (hzero ▸ hm)

include hzero in
/-- Actual top-kernel elements commute, even though their block top can
have odd order. -/
theorem commute (x y : (top C).ker) : Commute x y := by
  have hi (z : (top C).ker) : z⁻¹=z :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using square C hzero z)
  change x*y=y*x
  calc
    x*y=(x*y)⁻¹ := (hi (x*y)).symm
    _=y⁻¹*x⁻¹ := mul_inv_rev _ _
    _=y*x := by rw [hi,hi]

/-- Literal local homomorphism, available without a rank-one hypothesis. -/
def localProjection (i : Fin 4) : (top C).ker →* Linear where
  toFun x := ((x : C) : Frame).left i
  map_one' := rfl
  map_mul' x y := by
    have ht : ((x : C) : Frame).right=1 := x.property
    change (((x : C) : Frame)*((y : C) : Frame)).left i=_
    rw [PermutationalWreathProduct.mul_left]
    simp only [Pi.mul_apply,ht,inv_one,one_smul]

include hzero in
/-- One actual cubic in the local stabilizer kills this coordinate of
EVERY element of the actual top kernel. -/
theorem local_trivial (i : Fin 4) (q : C)
    (hq : (q : Frame).right i=i)
    (hqc : (q : Frame).left i^3=1) (hqn : (q : Frame).left i≠1)
    (x : (top C).ker) : localProjection C i x=1 := by
  let y := (MulAut.conjNormal q : MulAut (top C).ker) x
  have ht : ((x : C) : Frame).right=1 := x.property
  have hqi : (q : Frame).right⁻¹ i=i := by
    have he := congrArg (q : Frame).right.symm hq
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hy : localProjection C i y=(q : Frame).left i*localProjection C i x*((q : Frame).left i)⁻¹ := by
    change (((q : Frame)*((x : C) : Frame)*(q : Frame)⁻¹).left i)=_
    simp only [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
      PermutationalWreathProduct.inv_left,Pi.mul_apply,ht,mul_one]
    change (q : Frame).left i*((x : C) : Frame).left ((q : Frame).right⁻¹ i)*
      ((q : Frame).left ((q : Frame).right ((q : Frame).right⁻¹ i)))⁻¹=_
    rw [hqi,hq]
    rfl
  have hx2 : localProjection C i x^2=1 := by rw [← map_pow,square C hzero,map_one]
  have hc := congrArg (localProjection C i) (commute C hzero x y).eq
  simp only [map_mul,hy] at hc
  apply toThree_injective
  have hh := cubic_kills_commuting_involution (toThree (localProjection C i x))
    (toThree ((q : Frame).left i))
    (by rw [← map_pow,hx2,map_one])
    (by rw [← map_pow,hqc,map_one])
    (fun h => hqn (toThree_injective (h.trans (map_one _).symm)))
    (by simpa only [map_mul,map_inv] using congrArg toThree hc)
  simpa only [map_one] using hh

include hzero in
/-- If every local stabilizer has a cubic, the ACTUAL top map is
injective; no complement of a binary top kernel is assumed. -/
theorem top_injective
    (hcubic : ∀ i : Fin 4, ∃ q : C, (q : Frame).right i=i ∧
      (q : Frame).left i^3=1 ∧ (q : Frame).left i≠1) : Function.Injective (top C) := by
  apply (top C).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  let z : (top C).ker := ⟨x,hx⟩
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply PermutationalWreathProduct.ext
  · funext i
    obtain ⟨q,hq,hqc,hqn⟩ := hcubic i
    exact local_trivial C hzero i q hq hqc hqn z
  · exact hx

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddTopKernel
