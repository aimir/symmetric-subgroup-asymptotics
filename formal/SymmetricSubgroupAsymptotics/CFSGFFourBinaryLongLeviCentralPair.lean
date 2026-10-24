import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviRootActions

/-! The actual folded long Levi generator introduces the genuine
central a*t^2 correction on its paired radical coordinate. The proof
collects the same actual X/Y root products, retaining the literal centre;
it does not infer this correction from a proposed quadratic module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralPair
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGExceptionalHeisenbergRootRelations CFSGExceptionalHeisenbergProduct
open CFSGFiniteCommutingParameterHom CFSGHeisenbergCoordinateGroup
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourBinaryLongLeviRootActions
local instance fFourBinaryCentralPairRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev px (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  xHom A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private abbrev py (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private abbrev pz (K : Type) [CommRing K] (t : K) : U K :=
  zHom A hd hs hp ho configuration K (Multiplicative.ofAdd t)

private theorem conjugate_from_commutator {G : Type*} [Group G] (g x y : G)
    (hxy : Commute x y) (h : g*x*g⁻¹*x⁻¹=y) : g*x*g⁻¹=x*y := by
  calc
    _ = (g*x*g⁻¹*x⁻¹)*x := by group
    _ = y*x := by rw [h]
    _ = x*y := hxy.eq.symm

private theorem normalized_single_collect (K : Type) [CommRing K]
    (j : Fin 10) (s t : K) : py K j s*px K j t=px K j t*py K j s*pz K (s*t) := by
  have hx : X A hd hs hp ho configuration K (Multiplicative.ofAdd (Pi.single j t))=px K j t :=
    parameterHom_single _ _ j t
  have hy : Y A hd hs hp ho configuration K (Multiplicative.ofAdd (Pi.single j s))=py K j s :=
    parameterHom_single _ _ j s
  have hd0 : dot (Pi.single j s) (Pi.single j t)=s*t := by
    simp [dot,Pi.single_apply]
  have h := collecting A hd hs hp ho configuration K (Pi.single j t) (Pi.single j s)
  simpa only [hx,hy,hd0] using h

theorem long_positive_conjugate_pair (K : Type) [CommRing K] [CharP K 2] (a t : K) :
    canonicalRoot realizationData K false 2 a*(px K 6 t*px K 8 t)*
        (canonicalRoot realizationData K false 2 a)⁻¹ =
      px K 6 t*px K 8 t*py K 6 (a*t)*py K 8 (a*t)*pz K (a*t^2) := by
  let g : U K := canonicalRoot realizationData K false 2 a
  have h6 : g*px K 6 t*g⁻¹=px K 6 t*py K 8 (a*t) := by
    apply conjugate_from_commutator
    · exact cross_commute A hd hs hp ho configuration K 6 8 (by decide) t (-(a*t))
    · exact long_positive_commutator K 0 a t
  have h8 : g*px K 8 t*g⁻¹=px K 8 t*py K 6 (a*t) := by
    apply conjugate_from_commutator
    · exact cross_commute A hd hs hp ho configuration K 8 6 (by decide) t (-(a*t))
    · exact long_positive_commutator K 1 a t
  have hcollect : py K 8 (a*t)*px K 8 t=px K 8 t*py K 8 (a*t)*pz K (a*t^2) := by
    have h := normalized_single_collect K 8 (a*t) t
    have he : (a*t)*t=a*t^2 := by ring
    simpa only [he] using h
  have hz : Commute (pz K (a*t^2)) (py K 6 (a*t)) :=
    (y_central A hd hs hp ho configuration K 6 (-(a*t)) (a*t^2)).symm
  have hy : Commute (py K 8 (a*t)) (py K 6 (a*t)) :=
    y_commute A hd hs hp ho configuration K 8 6 (-(a*t)) (-(a*t))
  change g*(px K 6 t*px K 8 t)*g⁻¹ = _
  calc
    _ = (g*px K 6 t*g⁻¹)*(g*px K 8 t*g⁻¹) := by group
    _ = (px K 6 t*py K 8 (a*t))*(px K 8 t*py K 6 (a*t)) := by rw [h6,h8]
    _ = px K 6 t*(py K 8 (a*t)*px K 8 t)*py K 6 (a*t) := by group
    _ = px K 6 t*(px K 8 t*py K 8 (a*t)*pz K (a*t^2))*py K 6 (a*t) := by rw [hcollect]
    _ = (px K 6 t*px K 8 t)*py K 8 (a*t)*(pz K (a*t^2)*py K 6 (a*t)) := by group
    _ = (px K 6 t*px K 8 t)*py K 8 (a*t)*(py K 6 (a*t)*pz K (a*t^2)) := by rw [hz.eq]
    _ = (px K 6 t*px K 8 t)*(py K 8 (a*t)*py K 6 (a*t))*pz K (a*t^2) := by group
    _ = (px K 6 t*px K 8 t)*(py K 6 (a*t)*py K 8 (a*t))*pz K (a*t^2) := by rw [hy.eq]
    _ = _ := by group

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralPair
