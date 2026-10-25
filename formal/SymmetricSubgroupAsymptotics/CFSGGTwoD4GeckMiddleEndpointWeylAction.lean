import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointRootSections
import SymmetricSubgroupAsymptotics.ScalarPlaneAxisHom

/-! The actual normalizing short Weyl word swaps the two endpoint axes
with nonzero primitive coefficients. Full additivity follows from the
proved characteristic-kernel descent and the two genuine root sections;
no rank-one group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointWeylAction
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityD4CubeComplement
open CFSGTrialityGeckShortOrbitCommutator CFSGGTwoD4GeckMiddleCubicCurveWords
open CFSGGTwoD4GeckMiddleCubicFixedLifts CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleEndpointProjection CFSGGTwoD4GeckMiddleEndpointNormalizerAction
open CFSGGTwoD4GeckMiddleWeylCubeSigns CFSGGTwoD4GeckMiddleEndpointRootSections
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem curve_zero (K : Type) [Field K] (b : K) :
    curveWord K b 0 = cubeWord K zeroCube b := by
  simp only [curveWord,ordered_equal_short,shortOrbit_zero,one_mul,inv_one,mul_one]

private theorem endpoint_first (K : Type) [Field K] [Finite K]
    (u : fixedMiddle K) (t : K) (hu : coordinate K u = Pi.single 0 t) :
    endpointHom K u = Multiplicative.ofAdd ![t,0] := by
  change endpointLinear K (coordinate K u) = ![t,0]
  rw [hu]
  funext i
  fin_cases i
  · change ((Pi.single 0 t : Fin 4 → K) 0) = t
    simp only [Pi.single_eq_same]
  · change ((Pi.single 0 t : Fin 4 → K) 3) = 0
    simp only [Pi.single_apply,Fin.reduceEq,if_false]

private theorem endpoint_last (K : Type) [Field K] [Finite K]
    (u : fixedMiddle K) (t : K) (hu : coordinate K u = Pi.single 3 t) :
    endpointHom K u = Multiplicative.ofAdd ![0,t] := by
  change endpointLinear K (coordinate K u) = ![0,t]
  rw [hu]
  funext i
  fin_cases i
  · change ((Pi.single 3 t : Fin 4 → K) 0) = 0
    simp only [Pi.single_apply,Fin.reduceEq,if_false]
  · change ((Pi.single 3 t : Fin 4 → K) 3) = t
    simp only [Pi.single_eq_same]

theorem endpoint_weyl_swap (K : Type) [Field K] [Finite K] [CharP K 3]
    (hcard : 4 ≤ Nat.card K) : ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ ∀ v : Fin 2 → K,
      endpointAction K hcard (shortWeylElement K) (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd ![a*v 1,b*v 0] := by
  obtain ⟨d,hd,hcoord⟩ := final_root_coordinates
  obtain ⟨e0,he0,hword0⟩ := shortWeyl_cube_sign zeroCube
  obtain ⟨e1,he1,hword1⟩ := shortWeyl_cube_sign (cubeBits 7)
  have hlast : complement zeroCube = cubeBits 7 := by decide +kernel
  have hfirst : complement (cubeBits 7) = zeroCube := by decide +kernel
  let F := endpointAction K hcard (shortWeylElement K)
  let a : K := (e1 : K)*(d : K)
  let b : K := (d : K)*(e0 : K)
  have hdK : (d : K) ≠ 0 := by rcases hd with rfl | rfl <;> simp
  have he0K : (e0 : K) ≠ 0 := by rcases he0 with rfl | rfl <;> simp
  have he1K : (e1 : K) ≠ 0 := by rcases he1 with rfl | rfl <;> simp
  refine ⟨a,b,mul_ne_zero he1K hdK,mul_ne_zero hdK he0K,?_⟩
  have h0 (t : K) : F (Multiplicative.ofAdd ![t,0]) = Multiplicative.ofAdd ![0,b*t] := by
    let u := curveElement K t 0
    let w := (fixedMiddle K).normalizerMonoidHom (shortWeylElement K) u
    have hu : u.val = cubeWord K zeroCube t := curve_zero K t
    have hpu := endpoint_first K u t (first_root_coordinate K u t hu)
    have hw : w.val = cubeWord K (cubeBits 7) ((e0 : K)*t) := by
      change shortWeyl K*u.val*(shortWeyl K)⁻¹ = _
      rw [hu,hword0 K t,hlast]
    have hpw := endpoint_last K w ((d : K)*((e0 : K)*t))
      (hcoord K w ((e0 : K)*t) hw)
    have h := endpointAction_apply K hcard (shortWeylElement K) u
    rw [hpu] at h
    exact h.trans (hpw.trans (congrArg (fun z : K => Multiplicative.ofAdd ![0,z]) (by dsimp [b]; ring)))
  have h1 (t : K) : F (Multiplicative.ofAdd ![0,t]) = Multiplicative.ofAdd ![a*t,0] := by
    let u := finalRootElement K ((d : K)*t)
    let w := (fixedMiddle K).normalizerMonoidHom (shortWeylElement K) u
    have hd2 : (d : K)*((d : K)*t) = t := by rcases hd with rfl | rfl <;> simp
    have hc := hcoord K u ((d : K)*t) rfl
    rw [hd2] at hc
    have hpu := endpoint_last K u t hc
    have hw : w.val = cubeWord K zeroCube ((e1 : K)*((d : K)*t)) := by
      change shortWeyl K*cubeWord K (cubeBits 7) ((d : K)*t)*(shortWeyl K)⁻¹ = _
      rw [hword1 K ((d : K)*t),hfirst]
    have hpw := endpoint_first K w ((e1 : K)*((d : K)*t))
      (first_root_coordinate K w _ hw)
    have h := endpointAction_apply K hcard (shortWeylElement K) u
    rw [hpu] at h
    exact h.trans (hpw.trans (congrArg (fun z : K => Multiplicative.ofAdd ![z,0]) (by dsimp [a]; ring)))
  intro v
  exact ScalarPlaneAxisHom.apply_of_axis_values F.toMonoidHom a b h0 h1 v

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointWeylAction
