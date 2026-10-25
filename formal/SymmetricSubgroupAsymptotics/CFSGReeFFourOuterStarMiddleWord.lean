import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleCoordinates
import SymmetricSubgroupAsymptotics.CFSGConjugationActionGraph

/-! Literal short-word conjugation on the selected E6 root subgroup.
An intertwining pair keeps each actual root/Weyl unit together with its
proved coordinate action, so no single-column equality is promoted to
a group identity. The other head pieces remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleWord
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreQuadraticMatrix
open CFSGReeFFourOuterStarColumns CFSGReeFFourOuterStarConjugation
open CFSGReeFFourOuterStarMiddleCoordinates CFSGConjugationActionGraph

private abbrev tagAction (K : Type) [Field K] :
    AddAut (Fin 4 → K) →* MulAut (Multiplicative (Fin 4 → K)) :=
  (MulAutMultiplicative (Fin 4 → K)).symm.toMonoidHom

private abbrev graph (K : Type) [Field K] :=
  intertwiningPairs (tagAction K) (starHom K)

private def simplePair (K : Type) [Field K] [CharP K 2] (j : Fin 3) : graph K :=
  ⟨(shearCoordinates K j 1,canonicalRoot rawData K false (leftStar.step j) 1),by
    intro p
    exact mul_inv_eq_iff_eq_mul.mp (simple_conjugate K j 1 p.toAdd)⟩

private def weylPair (K : Type) [Field K] [CharP K 2] (j : Fin 3) : graph K :=
  ⟨(swapCoordinates K j,canonicalWeyl rawData K (leftStar.step j)),by
    intro p
    exact mul_inv_eq_iff_eq_mul.mp (weyl_conjugate K j p.toAdd)⟩

private abbrev U (K : Type) [Field K] (j : Fin 3) :=
  canonicalRoot rawData K false (leftStar.step j) 1
private abbrev W (K : Type) [Field K] (j : Fin 3) :=
  canonicalWeyl rawData K (leftStar.step j)

def rawY (K : Type) [Field K] : (Matrix GeckIndex GeckIndex K)ˣ :=
  U K 0*U K 2*U K 1*((W K 0*W K 2)*U K 1*(W K 0*W K 2)⁻¹)

def rawW (K : Type) [Field K] : (Matrix GeckIndex GeckIndex K)ˣ :=
  W K 0*W K 2*W K 1*W K 0*W K 2*W K 1

def rawR (K : Type) [Field K] : (Matrix GeckIndex GeckIndex K)ˣ :=
  rawW K*(rawY K)^2

private def yPair (K : Type) [Field K] [CharP K 2] : graph K :=
  simplePair K 0*simplePair K 2*simplePair K 1*
    ((weylPair K 0*weylPair K 2)*simplePair K 1*(weylPair K 0*weylPair K 2)⁻¹)

private def wPair (K : Type) [Field K] [CharP K 2] : graph K :=
  weylPair K 0*weylPair K 2*weylPair K 1*weylPair K 0*weylPair K 2*weylPair K 1

private theorem pair_conjugate (K : Type) [Field K] (p : graph K)
    (e : AddAut (Fin 4 → K)) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (he : p.val.1=e) (hg : p.val.2=g) (v : Fin 4 → K) :
    g*starHom K (Multiplicative.ofAdd v)*g⁻¹=
      starHom K (Multiplicative.ofAdd (e v)) := by
  have hp := p.property (Multiplicative.ofAdd v)
  change p.val.2*starHom K (Multiplicative.ofAdd v)=
    starHom K (Multiplicative.ofAdd (p.val.1 v))*p.val.2 at hp
  rw [he,hg] at hp
  exact mul_inv_eq_iff_eq_mul.mpr hp

theorem rawY_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 4 → K) :
    rawY K*starHom K (Multiplicative.ofAdd v)*(rawY K)⁻¹=
      starHom K (Multiplicative.ofAdd (coordinateY K v)) :=
  pair_conjugate K (yPair K) (coordinateY K) (rawY K) rfl rfl v

theorem rawW_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 4 → K) :
    rawW K*starHom K (Multiplicative.ofAdd v)*(rawW K)⁻¹=
      starHom K (Multiplicative.ofAdd (coordinateW K v)) :=
  pair_conjugate K (wPair K) (coordinateW K) (rawW K) rfl rfl v

theorem rawR_conjugate (K : Type) [Field K] [CharP K 2] (v : Fin 4 → K) :
    rawR K*starHom K (Multiplicative.ofAdd v)*(rawR K)⁻¹=
      starHom K (Multiplicative.ofAdd (coordinateR K v)) :=
  pair_conjugate K (wPair K*(yPair K)^2) (coordinateR K) (rawR K) rfl rfl v

theorem selected_parameter_conjugate (K : Type) [Field K] [CharP K 2] (a : K) :
    rawY K*starHom K (Multiplicative.ofAdd (Pi.single 0 a))*(rawY K)⁻¹=
      rawR K*starHom K (Multiplicative.ofAdd (Pi.single 0 a))*(rawR K)⁻¹ := by
  rw [rawY_conjugate,rawR_conjugate,selected_Y_eq_R]

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleWord
