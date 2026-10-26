import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeConjugation
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleWord

/-! The node-1 wedge component of the selected WHOLE outer-word y/r
relation. Exact root-group conjugation, not one-vector matrix evidence,
is propagated by an intertwining graph. No head-rank claim is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeMiddleWord
open CFSGReeFFourOuterWedgeConjugation CFSGReeFFourOuterWedgeRootData
open CFSGReeFFourOuterWedgeRootActions CFSGReeFFourOuterStarColumns
open CFSGReeFFourOuterStarMiddleWord CFSGConjugationActionGraph
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreQuadraticMatrix
private abbrev C (K : Type) [Field K] (j : Fin 3) : AddAut (Fin 6→K) :=
  shearCoordinates K j 1
private abbrev S (K : Type) [Field K] (j : Fin 3) : AddAut (Fin 6→K) :=
  swapCoordinates K j

private theorem source_target_ne (j : Fin 3) (b : Fin 2) :
    raiseTarget j b≠raiseSource j b := by fin_cases j <;> fin_cases b <;> decide

private theorem shear_apply (K : Type) [Field K] (j : Fin 3) (t : K) (v : Fin 6→K) :
    shearCoordinates K j t v=
      (v+Pi.single (raiseTarget j 1) (t*v (raiseSource j 1)))+
        Pi.single (raiseTarget j 0)
          (t*((v+Pi.single (raiseTarget j 1) (t*v (raiseSource j 1)) : Fin 6→K) (raiseSource j 0))) := by
  change (CFSGTypeAElementaryMatrices.elementary (source_target_ne j 0) t).toLin'
    ((CFSGTypeAElementaryMatrices.elementary (source_target_ne j 1) t).toLin' v)=_
  rw [CFSGAdditiveParameterConjugation.elementary_apply,
    CFSGAdditiveParameterConjugation.elementary_apply]

private theorem swap_apply (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) (k : Fin 6) :
    swapCoordinates K j v k=v ((wedgeSwap j).symm k) := rfl

private theorem swap_inverse (K : Type) [Field K] (j : Fin 3) : (S K j)⁻¹=S K j := by
  ext v k
  fin_cases j <;> fin_cases k <;> rfl

def coordinateY (K : Type) [Field K] : AddAut (Fin 6→K) :=
  C K 0*C K 2*C K 1*((S K 0*S K 2)*C K 1*(S K 0*S K 2)⁻¹)

def coordinateW (K : Type) [Field K] : AddAut (Fin 6→K) :=
  S K 0*S K 2*S K 1*S K 0*S K 2*S K 1

def coordinateR (K : Type) [Field K] : AddAut (Fin 6→K) :=
  coordinateW K*(coordinateY K)^2

private def act (K : Type) [Field K] (g : AddAut (Fin 6→K)) (v : Fin 6→K) : Fin 6→K := g v

private theorem act_mul (K : Type) [Field K] (g h : AddAut (Fin 6→K)) (v : Fin 6→K) :
    act K (g*h) v=act K g (act K h v) := rfl

private theorem act_inv_swap (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) :
    act K ((S K j)⁻¹) v=act K (S K j) v :=
  congrArg (fun g : AddAut (Fin 6→K)=>act K g v) (swap_inverse K j)

private theorem act_shear (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) :
    act K (C K j) v=
      (v+Pi.single (raiseTarget j 1) (v (raiseSource j 1)))+
        Pi.single (raiseTarget j 0)
          ((v+Pi.single (raiseTarget j 1) (v (raiseSource j 1)) : Fin 6→K) (raiseSource j 0)) := by
  exact (shear_apply K j 1 v).trans (by simp only [one_mul])

private theorem act_swap (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) :
    act K (S K j) v=(fun k=>v ((wedgeSwap j).symm k)) := rfl

private theorem C_apply (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) :
    act K (C K j) v=
      (![![v 0,v 1,v 2,v 3+v 1,v 4+v 2,v 5],
         ![v 0,v 1+v 0,v 2,v 3,v 4,v 5+v 4],
         ![v 0,v 1,v 2+v 1,v 3,v 4+v 3,v 5]] : Fin 3→Fin 6→K) j := by
  rw [act_shear]
  fin_cases j <;> ext k <;> fin_cases k <;>
    simp [raiseSource,raiseTarget,Pi.single_apply]

private theorem S_apply (K : Type) [Field K] (j : Fin 3) (v : Fin 6→K) :
    act K (S K j) v=
      (![![v 0,v 3,v 4,v 1,v 2,v 5],
         ![v 1,v 0,v 2,v 3,v 5,v 4],
         ![v 0,v 2,v 1,v 4,v 3,v 5]] : Fin 3→Fin 6→K) j := by
  rw [act_swap]
  fin_cases j <;> ext k <;> fin_cases k <;> rfl

private theorem four_zero (K : Type) [Field K] [CharP K 2] : (4 : K)=0 :=
  (CharP.cast_eq_zero_iff K 2 4).mpr (by decide)

private theorem coordinateY_apply (K : Type) [Field K] [CharP K 2] (v : Fin 6→K) :
    act K (coordinateY K) v=
      ![v 0,v 0+v 1,v 0+v 1+v 2,v 0+v 1+v 3,
        v 1+v 2+v 3+v 4,v 0+v 1+v 4+v 5] := by
  simp only [coordinateY,mul_inv_rev,act_mul,act_inv_swap,C_apply,S_apply]
  ext k
  fin_cases k <;> simp <;> ring_nf <;> simp [CharTwo.two_eq_zero,four_zero K]

private theorem coordinateW_apply (K : Type) [Field K] (v : Fin 6→K) :
    act K (coordinateW K) v=![v 5,v 4,v 2,v 3,v 1,v 0] := by
  simp only [coordinateW,act_mul,S_apply]
  ext k
  fin_cases k <;> rfl

theorem selected_Y_eq_R (K : Type) [Field K] [CharP K 2] (a : K) :
    act K (coordinateY K) (Pi.single 0 a)=act K (coordinateR K) (Pi.single 0 a) := by
  simp only [coordinateR,pow_two,act_mul,coordinateY_apply,coordinateW_apply]
  ext k
  fin_cases k <;> simp [Pi.single_apply] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero,four_zero K]

private abbrev tagAction (K : Type) [Field K] :
    AddAut (Fin 6→K)→*MulAut (Multiplicative (Fin 6→K)) :=
  (MulAutMultiplicative (Fin 6→K)).symm.toMonoidHom
private abbrev graph (K : Type) [Field K] := intertwiningPairs (tagAction K) (wedgeHom K)

private def simplePair (K : Type) [Field K] [CharP K 2] (j : Fin 3) : graph K :=
  ⟨(shearCoordinates K j 1,canonicalRoot rawData K false (leftStar.step j) 1),by
    intro p
    exact mul_inv_eq_iff_eq_mul.mp
      (CFSGReeFFourOuterWedgeConjugation.simple_conjugate K j 1 p.toAdd)⟩

private def weylPair (K : Type) [Field K] [CharP K 2] (j : Fin 3) : graph K :=
  ⟨(swapCoordinates K j,canonicalWeyl rawData K (leftStar.step j)),by
    intro p
    exact mul_inv_eq_iff_eq_mul.mp
      (CFSGReeFFourOuterWedgeConjugation.weyl_conjugate K j p.toAdd)⟩

private def yPair (K : Type) [Field K] [CharP K 2] : graph K :=
  simplePair K 0*simplePair K 2*simplePair K 1*
    ((weylPair K 0*weylPair K 2)*simplePair K 1*(weylPair K 0*weylPair K 2)⁻¹)
private def wPair (K : Type) [Field K] [CharP K 2] : graph K :=
  weylPair K 0*weylPair K 2*weylPair K 1*weylPair K 0*weylPair K 2*weylPair K 1

private theorem pair_conjugate (K : Type) [Field K] (p : graph K)
    (e : AddAut (Fin 6→K)) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (he : p.val.1=e) (hg : p.val.2=g) (v : Fin 6→K) :
    g*wedgeHom K (Multiplicative.ofAdd v)*g⁻¹=
      wedgeHom K (Multiplicative.ofAdd (e v)) := by
  have hpair := p.property (Multiplicative.ofAdd v)
  change p.val.2*wedgeHom K (Multiplicative.ofAdd v)=
    wedgeHom K (Multiplicative.ofAdd (p.val.1 v))*p.val.2 at hpair
  rw [he,hg] at hpair
  exact mul_inv_eq_iff_eq_mul.mpr hpair

theorem rawY_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 6→K) :
    rawY K*wedgeHom K (Multiplicative.ofAdd v)*(rawY K)⁻¹=
      wedgeHom K (Multiplicative.ofAdd (coordinateY K v)) :=
  pair_conjugate K (yPair K) (coordinateY K) (rawY K) rfl rfl v

theorem rawW_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 6→K) :
    rawW K*wedgeHom K (Multiplicative.ofAdd v)*(rawW K)⁻¹=
      wedgeHom K (Multiplicative.ofAdd (coordinateW K v)) :=
  pair_conjugate K (wPair K) (coordinateW K) (rawW K) rfl rfl v

theorem rawR_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 6→K) :
    rawR K*wedgeHom K (Multiplicative.ofAdd v)*(rawR K)⁻¹=
      wedgeHom K (Multiplicative.ofAdd (coordinateR K v)) :=
  pair_conjugate K (wPair K*(yPair K)^2) (coordinateR K) (rawR K) rfl rfl v

theorem selected_parameter_conjugate (K : Type) [Field K] [CharP K 2] (a : K) :
    rawY K*parameter K 0 a*(rawY K)⁻¹=rawR K*parameter K 0 a*(rawR K)⁻¹ := by
  have hh := (rawY_conjugate K (Pi.single 0 a)).trans
    ((congrArg (fun v : Fin 6→K=>wedgeHom K (Multiplicative.ofAdd v))
      (selected_Y_eq_R K a)).trans (rawR_conjugate K (Pi.single 0 a)).symm)
  simpa only [wedgeHom_single] using hh

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeMiddleWord
