import SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCentralLayers
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots

/-! The seven central coordinate axes are the literal central root and
three paired X/Y root words. This connects the actual central chart to
selected Levi root calculations without choosing a new parametrization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
open CFSGHeisenbergCoordinateGroup CFSGFiniteCommutingParameterHom
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergProduct
open CFSGExceptionalHeisenbergRootRelations CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourBinaryRadicalCentralLayers
open CFSGFFourBinaryRadicalCoordinates CFSGFFourE6HeisenbergLeviRoots
open CFSGFFourSerreMatrices
local instance fFourCentralWordsRootsDecidableEq : DecidableEq
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

private abbrev allX (K : Type) [CommRing K] (v : Fin 10 → K) : U K :=
  X A hd hs hp ho configuration K (Multiplicative.ofAdd v)
private abbrev allY (K : Type) [CommRing K] (v : Fin 10 → K) : U K :=
  Y A hd hs hp ho configuration K (Multiplicative.ofAdd v)

private theorem assemble_zero (K : Type) [Zero K] :
    assemble (0 : Fin 4 → K) (0 : Fin 3 → K)=0 := by
  funext i
  fin_cases i <;> rfl

private theorem assemble_single (K : Type) [AddZeroClass K] (i : Fin 3) (t : K) :
    assemble (0 : Fin 4 → K) (Pi.single i t) =
      Pi.single (pairPick i) t+Pi.single (partner (pairPick i)) t := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [assemble,pairPick,partner]

private theorem first_pair_product (K : Type) [CommRing K] (i : Fin 3) (t : K) :
    X A hd hs hp ho configuration K (Multiplicative.ofAdd (assemble 0 (Pi.single i t))) =
      px K (pairPick i) t*px K (partner (pairPick i)) t := by
  rw [assemble_single]
  exact ((X A hd hs hp ho configuration K).map_mul
    (Multiplicative.ofAdd (Pi.single (pairPick i) t))
    (Multiplicative.ofAdd (Pi.single (partner (pairPick i)) t))).trans
      (congrArg₂ (fun x y : U K => x*y)
        (parameterHom_single _ _ (pairPick i) t)
        (parameterHom_single _ _ (partner (pairPick i)) t))

private theorem second_pair_product (K : Type) [CommRing K] (i : Fin 3) (t : K) :
    Y A hd hs hp ho configuration K (Multiplicative.ofAdd (assemble 0 (Pi.single i t))) =
      py K (pairPick i) t*py K (partner (pairPick i)) t := by
  rw [assemble_single]
  exact ((Y A hd hs hp ho configuration K).map_mul
    (Multiplicative.ofAdd (Pi.single (pairPick i) t))
    (Multiplicative.ofAdd (Pi.single (partner (pairPick i)) t))).trans
      (congrArg₂ (fun x y : U K => x*y)
        (parameterHom_single _ _ (pairPick i) t)
        (parameterHom_single _ _ (partner (pairPick i)) t))

def centralMatrixHom (K : Type) [Field K] [CharP K 2] : CentralCoordinates K →* U K :=
  (CFSGFFourBinaryFixedRadicalEmbedding.matrixHom K).comp (centralCoordinates K)

theorem central_scalar_word (K : Type) [Field K] [CharP K 2] (c : K) :
    centralMatrixHom K (Multiplicative.ofAdd (c,(0 : Extra K)))=pz K c := by
  change allX K (assemble 0 0)*allY K (assemble 0 0)*pz K c = _
  rw [assemble_zero]
  have hx : allX K 0=1 := map_one _
  have hy : allY K 0=1 := map_one _
  rw [hx,hy,one_mul,one_mul]

theorem central_first_word (K : Type) [Field K] [CharP K 2] (i : Fin 3) (t : K) :
    centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,(0 : Fin 3 → K)))) =
      px K (pairPick i) t*px K (partner (pairPick i)) t := by
  change allX K (assemble 0 (Pi.single i t))*allY K (assemble 0 0)*pz K 0 = _
  rw [assemble_zero]
  have hy : allY K 0=1 := map_one _
  have hz : pz K 0=1 := map_one _
  rw [hy,hz,mul_one,mul_one]
  exact first_pair_product K i t

theorem central_second_word (K : Type) [Field K] [CharP K 2] (i : Fin 3) (t : K) :
    centralMatrixHom K (Multiplicative.ofAdd (0,((0 : Fin 3 → K),Pi.single i t))) =
      py K (pairPick i) t*py K (partner (pairPick i)) t := by
  change allX K (assemble 0 0)*allY K (assemble 0 (Pi.single i t))*pz K 0 = _
  rw [assemble_zero]
  have hx : allX K 0=1 := map_one _
  have hz : pz K 0=1 := map_one _
  rw [hx,hz,one_mul,mul_one]
  exact second_pair_product K i t

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
