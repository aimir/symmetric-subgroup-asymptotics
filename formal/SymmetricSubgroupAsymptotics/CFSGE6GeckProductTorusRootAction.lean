import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration

/-! The genuine raw E6 product torus scales every selected root parameter
and preserves every positive height tail. These are matrix-group facts
over every field; no original projective simplicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGE6GeckProductTorus
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoCoordinateRootHeightFiltration
open CFSGProductTorusAction CFSGIntegerMatrixPowerHom CFSGNormTwoGeckTorusHom
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

abbrev rawSelectedRoot (K : Type) [Field K] (k : Roots A) (a : K) :
    (Matrix GeckIndex GeckIndex K)ˣ := selectedRootElement A hd hs hp ho K k a

abbrev rawSelectedRootHom (K : Type) [Field K] (k : Roots A) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ := selectedRootHom A hd hs hp ho K k

def rootCharacter (K : Type) [Field K] (x : Fin 6→Kˣ) (k : Roots A) : Kˣ :=
  ∏j,x j^integerPairing A (E6Index j : Roots A).val k.val

theorem product_torus_selected_root_action (K : Type) [Field K]
    (x : Fin 6→Kˣ) (k : Roots A) (a : K) :
    rawProductTorus K x*rawSelectedRoot K k a*(rawProductTorus K x)⁻¹=
      rawSelectedRoot K k (a*(rootCharacter K x k : K)) := by
  let B : Matrix (Fin 6) (Fin 6) ℤ := fun _ j=>integerPairing A (E6Index j : Roots A).val k.val
  have hact (j : Fin 6) (t : Kˣ) (_ : Fin 6) (b : K) :
      simpleTorusHom K j t*rawSelectedRootHom K k (Multiplicative.ofAdd b)*
        (simpleTorusHom K j t)⁻¹=
      rawSelectedRootHom K k (Multiplicative.ofAdd (b*(t : K)^B 0 j)) := by
    simp only [simpleTorusHom,parameterTorusHom_apply]
    exact torus_conjugate_selected_root A hd hs hp ho K j t k b
  exact product_action (simpleTorusHom K) (simple_tori_commute K) B
    (fun _=>rawSelectedRootHom K k) hact x 0 a

theorem product_torus_heightTail_image_le (K : Type) [Field K]
    (x : Fin 6→Kˣ) (h : ℤ) :
    (heightTail A hd hs hp ho K h).map (MulAut.conj (rawProductTorus K x)).toMonoidHom≤
      heightTail A hd hs hp ho K h := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k,hk,a,rfl⟩
  change rawProductTorus K x*rawSelectedRoot K k.val a*
    (rawProductTorus K x)⁻¹∈heightTail A hd hs hp ho K h
  rw [product_torus_selected_root_action]
  exact rootElement_mem_heightTail A hd hs hp ho K h k.val k.property hk _

theorem product_torus_heightTail_image_eq (K : Type) [Field K] [Finite K]
    (x : Fin 6→Kˣ) (h : ℤ) :
    (heightTail A hd hs hp ho K h).map (MulAut.conj (rawProductTorus K x)).toMonoidHom=
      heightTail A hd hs hp ho K h := by
  apply Subgroup.eq_of_le_of_card_ge (product_torus_heightTail_image_le K x h)
  exact (Nat.card_congr ((MulAut.conj (rawProductTorus K x)).subgroupMap
    (heightTail A hd hs hp ho K h)).toEquiv).le

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
