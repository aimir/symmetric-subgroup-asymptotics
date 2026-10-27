import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import SymmetricSubgroupAsymptotics.JankoTwoStandardPairPresentationEquivalence
import SymmetricSubgroupAsymptotics.TernaryHeisenbergSingerGeneratorFrame
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts05
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts08
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts09
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts10
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts11
import Mathlib.Algebra.Group.Units.Hom

/-! The selected whole14/F5 identities and compatible Heisenberg/Singer frame in genuine units. No target simplicity, order, model identification or normalizer splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedMatrixIdentities
open CFSGJankoTwoSelectedPositiveWords
abbrev M := Matrix (Fin 14) (Fin 14) (ZMod 5)
abbrev Image := Mˣ
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

def unitA : Image where
  val := A
  inv := A
  val_inv := by simpa only [pow_two] using CFSGJankoTwoSelectedSeedPowerPilot.wholeA_square
  inv_val := by simpa only [pow_two] using CFSGJankoTwoSelectedSeedPowerPilot.wholeA_square

def unitB : Image where
  val := B
  inv := B^2
  val_inv := (pow_succ' B 2).symm.trans CFSGJankoTwoSelectedSeedPowerPilot.wholeB_cube
  inv_val := (pow_succ B 2).symm.trans CFSGJankoTwoSelectedSeedPowerPilot.wholeB_cube

theorem unitA_square : unitA^2=1 := by
  apply Units.ext
  change A^2=1
  exact CFSGJankoTwoSelectedSeedPowerPilot.wholeA_square

theorem unitB_cube : unitB^3=1 := by
  apply Units.ext
  change B^3=1
  exact CFSGJankoTwoSelectedSeedPowerPilot.wholeB_cube

private theorem unitA_inverse : unitA⁻¹=unitA :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using unitA_square)

private theorem unitB_inverse : unitB⁻¹=unitB^2 :=
  inv_eq_of_mul_eq_one_right ((pow_succ' unitB 2).symm.trans unitB_cube)

private theorem value000 : ((node000 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.A_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node000 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedBaseCaches.A_source_binding

private theorem value001 : ((node001 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.B_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node001 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedBaseCaches.B_source_binding

private theorem value002 : ((node002 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node002 (Units.coeHom M) unitA unitB).trans
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm)

private theorem value021 : ((node021 unitA unitB) : M)=CFSGJankoTwoSelectedCaches03.C021_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node021 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts02.matrix_node021

private theorem value027 : ((node027 unitA unitB) : M)=CFSGJankoTwoSelectedCaches04.C027_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node027 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts03.matrix_node027

private theorem value029 : ((node029 unitA unitB) : M)=CFSGJankoTwoSelectedCaches04.C029_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node029 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts03.matrix_node029

private theorem value035 : ((node035 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C035_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node035 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts04.matrix_node035

private theorem value038 : ((node038 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node038 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts04.matrix_node038

private theorem value040 : ((node040 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node040 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts04.matrix_node040

private theorem value042 : ((node042 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node042 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts04.matrix_node042

private theorem value043 : ((node043 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C043_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node043 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node043

private theorem value044 : ((node044 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C043_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node044 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node044

private theorem value045 : ((node045 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C045_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node045 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node045

private theorem value046 : ((node046 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C045_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node046 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node046

private theorem value047 : ((node047 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C047_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node047 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node047

private theorem value049 : ((node049 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C047_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node049 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node049

private theorem value050 : ((node050 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C050_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node050 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts05.matrix_node050

private theorem value053 : ((node053 unitA unitB) : M)=CFSGJankoTwoSelectedCaches05.C050_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node053 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts06.matrix_node053

private theorem value054 : ((node054 unitA unitB) : M)=CFSGJankoTwoSelectedCaches06.C054_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node054 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts06.matrix_node054

private theorem value055 : ((node055 unitA unitB) : M)=CFSGJankoTwoSelectedCaches06.C054_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node055 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts06.matrix_node055

private theorem value056 : ((node056 unitA unitB) : M)=CFSGJankoTwoSelectedCaches06.C056_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node056 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts06.matrix_node056

private theorem value057 : ((node057 unitA unitB) : M)=CFSGJankoTwoSelectedCaches06.C056_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node057 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts06.matrix_node057

private theorem value066 : ((node066 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node066 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts07.matrix_node066

private theorem value099 : ((node099 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node099 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts11.matrix_node099

private theorem value102 : ((node102 unitA unitB) : M)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 :=
  (CFSGJankoTwoSelectedPositiveWords.map_node102 (Units.coeHom M) unitA unitB).trans
    CFSGJankoTwoSelectedProducts11.matrix_node102

private theorem one_ab7 : (node066 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value066.trans value002.symm

private theorem one_comm12 : (node099 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value099.trans value002.symm

private theorem one_last3 : (node102 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value102.trans value002.symm

private theorem equation_x_cube : (node038 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value038.trans value002.symm

private theorem equation_y_cube : (node040 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value040.trans value002.symm

private theorem equation_z_cube : (node042 unitA unitB)=(node002 unitA unitB) := by
  apply Units.ext
  exact value042.trans value002.symm

private theorem equation_x_commutes_z : (node043 unitA unitB)=(node044 unitA unitB) := by
  apply Units.ext
  exact value043.trans value044.symm

private theorem equation_y_commutes_z : (node045 unitA unitB)=(node046 unitA unitB) := by
  apply Units.ext
  exact value045.trans value046.symm

private theorem equation_canonical_collect : (node047 unitA unitB)=(node049 unitA unitB) := by
  apply Units.ext
  exact value047.trans value049.symm

private theorem equation_singer_first : (node050 unitA unitB)=(node053 unitA unitB) := by
  apply Units.ext
  exact value050.trans value053.symm

private theorem equation_singer_second : (node054 unitA unitB)=(node055 unitA unitB) := by
  apply Units.ext
  exact value054.trans value055.symm

private theorem equation_singer_third : (node056 unitA unitB)=(node057 unitA unitB) := by
  apply Units.ext
  exact value056.trans value057.symm

theorem product_seventh : (unitA*unitB)^7=1 := by
  have h : (unitA*unitB)^7=(node066 unitA unitB) := by
    simpa only [node061,node000,node001] using (power056 unitA unitB)
  exact h.trans one_ab7

theorem commutator_twelfth : (CFSG.Models.commWord unitA unitB)^12=1 := by
  have hw : CFSG.Models.commWord unitA unitB=(node070 unitA unitB) := by
    simp only [CFSG.Models.commWord,unitA_inverse,unitB_inverse,pow_two,
      node070,node069,node068,node067,node059,node002,node000,node001,one_mul]
  rw [hw]
  exact (power063 unitA unitB).trans one_comm12

theorem last_relator : JankoTwoStandardPairPresentationEquivalence.lastRelator unitA unitB=1 := by
  have hw : JankoTwoStandardPairPresentationEquivalence.lastRelator unitA unitB=
      (node094 unitA unitB)^3 := by
    simp only [JankoTwoStandardPairPresentationEquivalence.lastRelator,unitB_inverse,
      pow_one,pow_two,node094,node093,node092,node091,node090,node089,node088,node087,node086,node085,node084,node083,node082,node081,node080,node079,node078,node077,node076,node075,node074,node073,node072,node071,node059,node002,node000,node001,one_mul]
  exact hw.trans ((power068 unitA unitB).trans one_last3)

theorem unitA_ne_one : unitA≠1 := by
  have hn : A (0 : Fin 14) (1 : Fin 14)≠(1 : M) 0 1 := by decide +kernel
  intro he
  exact hn (congrArg (fun u : Image => (u : M) 0 1) he)

def nativeFrame : TernaryHeisenbergSingerGeneratorFrame.Frame Image where
  x := (node021 unitA unitB)
  y := (node027 unitA unitB)
  z := (node035 unitA unitB)
  h := (node029 unitA unitB)
  x_cube := (power039 unitA unitB).trans equation_x_cube
  y_cube := (power044 unitA unitB).trans equation_y_cube
  z_cube := (power049 unitA unitB).trans equation_z_cube
  commute_xz := by
    simpa only [node044,node043] using equation_x_commutes_z
  commute_yz := by
    simpa only [node046,node045] using equation_y_commutes_z
  collect := by
    simpa only [node049,node048,node047] using equation_canonical_collect
  central_ne_one := by
    have hn : (CFSGJankoTwoSelectedCaches05.C035_data.matrix 5) (0 : Fin 14) (0 : Fin 14)≠(1 : M) 0 0 := by decide +kernel
    intro he
    have hm := congrArg (Units.coeHom M) he
    have hmOne := hm.trans (map_one (Units.coeHom M))
    have hcache := value035.symm.trans hmOne
    exact hn (congrArg (fun m : M => m 0 0) hcache)
  singer_x := by
    apply mul_inv_eq_iff_eq_mul.mpr
    simpa only [node053,node052,node051,node050,←power022] using equation_singer_first
  singer_y := by
    apply mul_inv_eq_iff_eq_mul.mpr
    simpa only [node055,node054] using equation_singer_second
  singer_z := by
    apply mul_inv_eq_iff_eq_mul.mpr
    simpa only [node057,node056,←power034] using equation_singer_third

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedMatrixIdentities
