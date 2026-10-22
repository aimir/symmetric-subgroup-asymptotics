import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement

/-! Exact additive parameter law for the selected literal root words.
This is valid over every coefficient ring, and includes the equal-root
commuting branch used in higher-height collection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem selectedRootElement_zero (K : Type) [CommRing K] (k : Roots A) :
    selectedRootElement A hd hs hp ho K k 0=1 := by
  simp only [selectedRootElement,rootWord,canonicalRoot_zero,mul_one,mul_inv_cancel]

theorem selectedRootElement_add (K : Type) [CommRing K] (k : Roots A) (a b : K) :
    selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K k b=
      selectedRootElement A hd hs hp ho K k (a+b) := by
  let p := rootWitness A hd hs hp ho k
  let u := canonicalWord D K p.val.1
  change (u*canonicalRoot D K true p.val.2 a*u⁻¹)*(u*canonicalRoot D K true p.val.2 b*u⁻¹)=
    u*canonicalRoot D K true p.val.2 (a+b)*u⁻¹
  calc
    _=u*(canonicalRoot D K true p.val.2 a*canonicalRoot D K true p.val.2 b)*u⁻¹ := by group
    _=_ := by rw [canonicalRoot_add]

theorem selectedRootElement_commute (K : Type) [CommRing K] (k : Roots A) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K k a) (selectedRootElement A hd hs hp ho K k b) := by
  change selectedRootElement A hd hs hp ho K k a*selectedRootElement A hd hs hp ho K k b=
    selectedRootElement A hd hs hp ho K k b*selectedRootElement A hd hs hp ho K k a
  rw [selectedRootElement_add,selectedRootElement_add,add_comm]

def selectedRootHom (K : Type) [CommRing K] (k : Roots A) :
    Multiplicative K→*(Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ where
  toFun a := selectedRootElement A hd hs hp ho K k a.toAdd
  map_one' := selectedRootElement_zero A hd hs hp ho K k
  map_mul' a b := (selectedRootElement_add A hd hs hp ho K k a.toAdd b.toAdd).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive
