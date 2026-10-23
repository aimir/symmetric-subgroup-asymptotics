import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
import Mathlib.Tactic.Group

/-! A displayed actual negative-simple Weyl-word chart parametrizes its
literal integral-degree root line additively. The subgroup identification
uses the proved integral sign/unit word-independence theorem; degree alone
in an ambient matrix algebra is not being used as root recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordParameterEquiv
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateAllRootParameters
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGSerreQuadraticWordRootTransport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
variable (k : Roots A) (w : List (Fin r)) (j : Fin r)
    (hdegree : wordLinear A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) w (-(Pi.single j (1:ℤ) : Fin r→ℤ))=k.val)

include hdegree

theorem wordParameter_mem (K : Type) [Field K] (t : K) :
    rootWord D K w true j t∈rootSubgroup A hd hs hp ho K k := by
  have hm : rootWord D K w true j t∈wordRootSubgroup A hd hs hp ho K w j :=
    (mem_wordRootSubgroup_iff A hd hs hp ho K w j _).mpr ⟨t,rfl⟩
  have he : rootSubgroup A hd hs hp ho K k=wordRootSubgroup A hd hs hp ho K w j :=
    rootSubgroup_eq_word A hd hs hp ho K k w j hdegree.symm
  exact he.symm ▸ hm

def wordParameter (K : Type) [Field K] (t : K) : rootSubgroup A hd hs hp ho K k :=
  ⟨rootWord D K w true j t,wordParameter_mem A hd hs hp ho k w j hdegree K t⟩

theorem wordParameter_surjective (K : Type) [Field K] :
    Function.Surjective (wordParameter A hd hs hp ho k w j hdegree K) := by
  intro x
  let y : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ := x.val
  have hy : y∈rootSubgroup A hd hs hp ho K k := x.property
  have he : rootSubgroup A hd hs hp ho K k=wordRootSubgroup A hd hs hp ho K w j :=
    rootSubgroup_eq_word A hd hs hp ho K k w j hdegree.symm
  have hx : y∈wordRootSubgroup A hd hs hp ho K w j :=
    Eq.mp (congrArg (fun H : Subgroup
      ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)=>y∈H) he) hy
  obtain ⟨t,ht⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K w j y).mp hx
  exact ⟨t,Subtype.ext ht⟩

theorem wordParameter_bijective (K : Type) [Field K] [Finite K] :
    Function.Bijective (wordParameter A hd hs hp ho k w j hdegree K) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨wordParameter_surjective A hd hs hp ho k w j hdegree K,?_⟩
  exact (rootSubgroup_card A hd hs hp ho K k).symm

def wordParameterHom (K : Type) [Field K] :
    Multiplicative K→*rootSubgroup A hd hs hp ho K k where
  toFun a:=wordParameter A hd hs hp ho k w j hdegree K a.toAdd
  map_one':=by
    apply Subtype.ext
    change rootWord D K w true j 0=1
    simp only [rootWord,canonicalRoot_zero,mul_one,mul_inv_cancel]
  map_mul' a b:=by
    apply Subtype.ext
    change rootWord D K w true j (a.toAdd+b.toAdd)=
      rootWord D K w true j a.toAdd*rootWord D K w true j b.toAdd
    simp only [rootWord]
    rw [←canonicalRoot_add D K true j a.toAdd b.toAdd]
    group

def wordParameterMulEquiv (K : Type) [Field K] [Finite K] :
    Multiplicative K≃*rootSubgroup A hd hs hp ho K k :=
  MulEquiv.ofBijective (wordParameterHom A hd hs hp ho k w j hdegree K)
    ((wordParameter_bijective A hd hs hp ho k w j hdegree K).comp Multiplicative.toAdd.bijective)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordParameterEquiv
