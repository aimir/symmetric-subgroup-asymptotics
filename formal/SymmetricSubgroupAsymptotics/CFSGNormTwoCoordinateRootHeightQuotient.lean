import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightCommutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Actual positive-root parameter homomorphisms in the successive height
quotients of the Geck MATRIX image-U. Their images commute by the proved
sum-height root commutator identity. Normality and commutativity are not
new assumptions of a factorization interface. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
open scoped commutatorElement
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightCommutator
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

abbrev PositiveGroup (K : Type) [Field K] := rootGroup A hs hp b₀ s₀ K false

def positiveRootParameterHom (K : Type) [Field K] (k : Roots A) (hk : ∀i,0≤k.val i) :
    Multiplicative K→*PositiveGroup A hd hs hp ho K :=
  (selectedRootHom A hd hs hp ho K k).codRestrict (PositiveGroup A hd hs hp ho K)
    (fun a=>selected_positive_root_mem A hd hs hp ho K k hk a.toAdd)

abbrev heightTailInPositive (K : Type) [Field K] (h : ℤ) :
    Subgroup (PositiveGroup A hd hs hp ho K) :=
  (heightTail A hd hs hp ho K h).subgroupOf (PositiveGroup A hd hs hp ho K)

local instance coordinateHeightTailNormal (K : Type) [Field K] (h : ℤ) :
    (heightTailInPositive A hd hs hp ho K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

abbrev HeightQuotient (K : Type) [Field K] (h : ℤ) :=
  PositiveGroup A hd hs hp ho K ⧸heightTailInPositive A hd hs hp ho K (h+1)

def quotientRootHom (K : Type) [Field K] (h : ℤ) (k : Roots A) (hk : ∀i,0≤k.val i) :
    Multiplicative K→*HeightQuotient A hd hs hp ho K h :=
  (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))).comp
    (positiveRootParameterHom A hd hs hp ho K k hk)

theorem quotient_root_images_commute (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (k l : Roots A) (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i)
    (hkheight : h≤height k.val) (hlheight : h≤height l.val) (a b : Multiplicative K) :
    Commute (quotientRootHom A hd hs hp ho K h k hk a)
      (quotientRootHom A hd hs hp ho K h l hl b) := by
  let N := heightTailInPositive A hd hs hp ho K (h+1)
  let q : PositiveGroup A hd hs hp ho K→*HeightQuotient A hd hs hp ho K h := QuotientGroup.mk' N
  let x := positiveRootParameterHom A hd hs hp ho K k hk a
  let y := positiveRootParameterHom A hd hs hp ho K l hl b
  have hcomm : x*y*x⁻¹*y⁻¹∈N := by
    change selectedRootElement A hd hs hp ho K k a.toAdd*selectedRootElement A hd hs hp ho K l b.toAdd*
      (selectedRootElement A hd hs hp ho K k a.toAdd)⁻¹*
        (selectedRootElement A hd hs hp ho K l b.toAdd)⁻¹∈heightTail A hd hs hp ho K (h+1)
    exact heightTail_antitone A hd hs hp ho K (by omega : h+1≤h+h)
      (root_commutator_mem_height_add A hd hs hp ho K h h k l hk hl hkheight hlheight a.toAdd b.toAdd)
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅q x,q y⁆=1
  rw [←map_commutatorElement q]
  exact (QuotientGroup.eq_one_iff ⁅x,y⁆).mpr hcomm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
