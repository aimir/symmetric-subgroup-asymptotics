import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeWeylCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylCentralAxes

/-! The actual two short F4 Weyl matrices lift the corresponding native
C3 actions on the SAME central chart. Every coordinate is paid by actual
selected-root identities; no full symplectic lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNativeCovariance
open CFSGFFourBinaryNativeCentralAction CFSGFFourBinaryLeviNativeWeylCoordinates
open CFSGFFourBinaryShortLeviWeylCentralAxes CFSGFFourBinaryShortLeviWeylRoots
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local instance fFourWeylNativeCovarianceRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
private abbrev Raw (K : Type) := K × ((Fin 3 → K) × (Fin 3 → K))
private def node : Fin 2 → Fin 4 := ![0,1]

private theorem single_comp_swap (K : Type) [Zero K] (n : Fin 2) (i : Fin 3) (t : K) :
    (Pi.single i t : Fin 3 → K) ∘ swapIndex n = Pi.single (swapIndex n i) t := by
  funext j
  fin_cases n <;> fin_cases i <;> fin_cases j <;>
    simp [swapIndex,Equiv.swap_apply_def,Function.comp_def,Pi.single_apply]

private theorem seven_axis_ext {K G : Type} [AddCommGroup K] [Group G]
    (f g : Multiplicative (Raw K) →* G)
    (hc : ∀ c, f (Multiplicative.ofAdd (c,(0,0)))=g (Multiplicative.ofAdd (c,(0,0))))
    (hu : ∀ (i : Fin 3) t, f (Multiplicative.ofAdd (0,(Pi.single i t,0)))=
      g (Multiplicative.ofAdd (0,(Pi.single i t,0))))
    (hv : ∀ (i : Fin 3) t, f (Multiplicative.ofAdd (0,(0,Pi.single i t)))=
      g (Multiplicative.ofAdd (0,(0,Pi.single i t)))) : f=g := by
  apply MonoidHom.ext
  intro x
  let c := x.toAdd.1
  let u := x.toAdd.2.1
  let v := x.toAdd.2.2
  have hu0 : u=Pi.single 0 (u 0)+Pi.single 1 (u 1)+Pi.single 2 (u 2) := by
    funext i
    fin_cases i <;> simp
  have hv0 : v=Pi.single 0 (v 0)+Pi.single 1 (v 1)+Pi.single 2 (v 2) := by
    funext i
    fin_cases i <;> simp
  have he : x =
      Multiplicative.ofAdd (c,(0,0)) *
      Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0)) *
      Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0)) *
      Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0)) *
      Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0))) *
      Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1))) *
      Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2))) := by
    apply Multiplicative.toAdd.injective
    change (c,(u,v)) =
      (c,(0,0))+(0,(Pi.single 0 (u 0),0))+(0,(Pi.single 1 (u 1),0))+
      (0,(Pi.single 2 (u 2),0))+(0,(0,Pi.single 0 (v 0)))+
      (0,(0,Pi.single 1 (v 1)))+(0,(0,Pi.single 2 (v 2)))
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simpa using hu0
      · simpa using hv0
  calc
    f x = f (Multiplicative.ofAdd (c,(0,0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0)))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1)))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2)))) := by
      rw [he,map_mul,map_mul,map_mul,map_mul,map_mul,map_mul]
    _ = g (Multiplicative.ofAdd (c,(0,0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0)))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1)))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2)))) := by
      rw [hc,hu,hu,hu,hv,hv,hv]
    _ = g x := by rw [he,map_mul,map_mul,map_mul,map_mul,map_mul,map_mul]

theorem weyl_central_covariance (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K=2) (n : Fin 2) (x : CentralCoordinates K) :
    canonicalWeyl realizationData K (node n) * centralMatrixHom K x *
        (canonicalWeyl realizationData K (node n))⁻¹ =
      centralMatrixHom K (nativeCentralAction K hK
        (CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc) x) := by
  let g := canonicalWeyl realizationData K (node n)
  let A := CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc
  have hh : (MulAut.conj g).toMonoidHom.comp (centralMatrixHom K) =
      (centralMatrixHom K).comp (nativeCentralAction K hK A).toMonoidHom := by
    apply seven_axis_ext
    · intro c
      change g*centralMatrixHom K (Multiplicative.ofAdd (c,(0,0)))*g⁻¹ =
        centralMatrixHom K (nativeCentralAction K hK A (Multiplicative.ofAdd (c,(0,0))))
      have he : nativeCentralAction K hK A (Multiplicative.ofAdd (c,(0,0))) =
          Multiplicative.ofAdd (c,(0,0)) := by
        apply (nativeCentralAction_weyl K hK n (Multiplicative.ofAdd (c,(0,0)))).trans
        rfl
      rw [he]
      exact short_weyl_central_scalar K n c
    · intro i t
      change g*centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,0)))*g⁻¹ =
        centralMatrixHom K (nativeCentralAction K hK A (Multiplicative.ofAdd (0,(Pi.single i t,0))))
      have he : nativeCentralAction K hK A (Multiplicative.ofAdd (0,(Pi.single i t,0))) =
          Multiplicative.ofAdd (0,(Pi.single (swapIndex n i) t,0)) := by
        apply (nativeCentralAction_weyl K hK n (Multiplicative.ofAdd (0,(Pi.single i t,0)))).trans
        apply Multiplicative.toAdd.injective
        change ((0 : K),((Pi.single i t : Fin 3 → K) ∘ swapIndex n,
          (0 : Fin 3 → K) ∘ swapIndex n)) = (0,(Pi.single (swapIndex n i) t,0))
        rw [single_comp_swap]
        rfl
      rw [he]
      exact short_weyl_central_first K n i t
    · intro i t
      change g*centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single i t)))*g⁻¹ =
        centralMatrixHom K (nativeCentralAction K hK A (Multiplicative.ofAdd (0,(0,Pi.single i t))))
      have he : nativeCentralAction K hK A (Multiplicative.ofAdd (0,(0,Pi.single i t))) =
          Multiplicative.ofAdd (0,(0,Pi.single (swapIndex n i) t)) := by
        apply (nativeCentralAction_weyl K hK n (Multiplicative.ofAdd (0,(0,Pi.single i t)))).trans
        apply Multiplicative.toAdd.injective
        change ((0 : K),((0 : Fin 3 → K) ∘ swapIndex n,
          (Pi.single i t : Fin 3 → K) ∘ swapIndex n)) = (0,(0,Pi.single (swapIndex n i) t))
        rw [single_comp_swap]
        rfl
      rw [he]
      exact short_weyl_central_second K n i t
  exact DFunLike.congr_fun hh x

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNativeCovariance
