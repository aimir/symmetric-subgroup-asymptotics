import SymmetricSubgroupAsymptotics.UnitsInverseValueUniqueness

import SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatricesPilot

import SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation



/-! ONE selected literal straightline certificate. Every cached matrix is

bound by original unit operations and49 checked natural dot products. -/

set_option autoImplicit false

noncomputable section

open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrices

open SmallNaturalMatrixProductReflection

abbrev Image := Matrix.GeneralLinearGroup (Fin 7) (ZMod 11)

private theorem alias_A : unitA=unitA := rfl

private theorem cache_A : (unitA : M)=matrixA := rfl

private theorem alias_B : unitB=unitB := rfl

private theorem cache_B : (unitB : M)=matrixB := rfl

private def raw_001 : Matrix (Fin 7) (Fin 7) ℕ := !![5,10,5,2,7,3,3;
  7,4,10,3,4,9,4;
  1,10,8,3,7,0,3;
  8,0,9,6,2,4,3;
  5,3,1,1,10,2,9;
  8,3,2,2,7,3,4;
  2,8,1,9,3,5,9]

private def mat_001 : M := castMatrix 11 7 raw_001

private theorem check_001 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawB i k * raw_001 k j) % 11 = (1 : Matrix (Fin 7) (Fin 7) ℕ) i j % 11 := by
  decide +kernel

private def u_001 : Image := unitB⁻¹

private theorem alias_001 : (unitB)⁻¹=u_001 := congrArg (fun x : Image => x⁻¹) alias_B

private theorem cache_001 : (u_001 : M)=mat_001 := by
  have hr : (unitB : M)*mat_001=1 :=
    (congrArg (fun x : M => x*mat_001) cache_B).trans
      ((mul_eq_of_mod_dot 11 7 rawB raw_001 1 check_001).trans (castMatrix_one 11 7))
  exact UnitsInverseValueUniqueness.inverse_val_eq_of_mul_eq_one _ _ hr

private def raw_002 : Matrix (Fin 7) (Fin 7) ℕ := !![9,9,2,1,3,8,6;
  2,5,5,9,2,2,1;
  5,9,9,9,8,10,3;
  5,5,7,10,9,2,5;
  7,1,5,3,5,8,2;
  6,9,10,1,10,2,3;
  1,9,6,5,9,5,4]

private def mat_002 : M := castMatrix 11 7 raw_002

private theorem check_002 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawA i k * rawB k j) % 11 = raw_002 i j % 11 := by
  decide +kernel

private def u_002 : Image := unitA*unitB

private theorem alias_002 : (unitA*unitB)=u_002 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_A alias_B

private theorem cache_002 : (u_002 : M)=mat_002 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_A cache_B).trans
    (mul_eq_of_mod_dot 11 7 rawA rawB raw_002 check_002)

private def raw_003 : Matrix (Fin 7) (Fin 7) ℕ := !![9,9,2,1,3,8,6;
  2,5,5,9,2,2,1;
  5,9,9,9,8,10,3;
  5,5,7,10,9,2,5;
  7,1,5,3,5,8,2;
  6,9,10,1,10,2,3;
  1,9,6,5,9,5,4]

private def mat_003 : M := castMatrix 11 7 raw_003

private theorem check_003 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawA i k * rawB k j) % 11 = raw_003 i j % 11 := by
  decide +kernel

private def u_003 : Image := unitA*unitB

private theorem alias_003 : (unitA*unitB)=u_003 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_A alias_B

private theorem cache_003 : (u_003 : M)=mat_003 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_A cache_B).trans
    (mul_eq_of_mod_dot 11 7 rawA rawB raw_003 check_003)

private def raw_004 : Matrix (Fin 7) (Fin 7) ℕ := !![10,5,6,7,6,7,5;
  6,5,4,6,6,4,1;
  6,3,3,3,6,8,5;
  7,3,6,0,4,8,6;
  5,3,0,3,7,5,7;
  6,5,7,4,10,5,5;
  4,3,3,6,5,0,4]

private def mat_004 : M := castMatrix 11 7 raw_004

private theorem check_004 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_003 i k * rawA k j) % 11 = raw_004 i j % 11 := by
  decide +kernel

private def u_004 : Image := u_003*unitA

private theorem alias_004 : ((unitA*unitB)*unitA)=u_004 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_003 alias_A

private theorem cache_004 : (u_004 : M)=mat_004 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_003 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_003 rawA raw_004 check_004)

private def raw_005 : Matrix (Fin 7) (Fin 7) ℕ := !![1,6,5,6,6,7,7;
  5,4,5,10,6,6,4;
  6,8,6,5,3,8,3;
  4,6,7,5,8,0,8;
  5,0,7,7,3,8,6;
  6,4,10,5,5,7,6;
  4,8,5,4,3,5,0]

private def mat_005 : M := castMatrix 11 7 raw_005

private theorem check_005 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_004 i k * raw_001 k j) % 11 = raw_005 i j % 11 := by
  decide +kernel

private def u_005 : Image := u_004*u_001

private theorem alias_005 : (((unitA*unitB)*unitA)*(unitB)⁻¹)=u_005 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_004 alias_001

private theorem cache_005 : (u_005 : M)=mat_005 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_004 cache_001).trans
    (mul_eq_of_mod_dot 11 7 raw_004 raw_001 raw_005 check_005)

private theorem pow_u_002_1 : ((unitA*unitB))^1=u_002 := (pow_one _).trans alias_002

private def raw_006 : Matrix (Fin 7) (Fin 7) ℕ := !![2,3,10,0,10,6,7;
  4,8,8,8,0,9,3;
  8,0,5,9,1,1,4;
  0,2,10,3,6,10,7;
  3,3,4,3,4,4,5;
  3,7,0,3,2,3,8;
  3,3,2,7,3,0,8]

private def mat_006 : M := castMatrix 11 7 raw_006

private theorem check_006 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_002 i k * raw_002 k j) % 11 = raw_006 i j % 11 := by
  decide +kernel

private def u_006 : Image := u_002*u_002

private theorem alias_006 : (((unitA*unitB))^1*(unitA*unitB))=u_006 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_1 alias_002

private theorem cache_006 : (u_006 : M)=mat_006 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_002 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_002 raw_002 raw_006 check_006)

private theorem pow_u_002_2 : ((unitA*unitB))^2=u_006 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_1 alias_002

private def raw_007 : Matrix (Fin 7) (Fin 7) ℕ := !![0,8,8,3,1,7,1;
  2,10,9,10,6,1,3;
  5,10,9,2,9,8,8;
  2,10,7,3,7,4,7;
  4,2,3,5,3,9,0;
  8,2,7,2,8,7,8;
  8,5,8,2,5,7,1]

private def mat_007 : M := castMatrix 11 7 raw_007

private theorem check_007 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_006 i k * raw_002 k j) % 11 = raw_007 i j % 11 := by
  decide +kernel

private def u_007 : Image := u_006*u_002

private theorem alias_007 : (((unitA*unitB))^2*(unitA*unitB))=u_007 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_2 alias_002

private theorem cache_007 : (u_007 : M)=mat_007 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_006 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_006 raw_002 raw_007 check_007)

private theorem pow_u_002_3 : ((unitA*unitB))^3=u_007 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_2 alias_002

private def raw_008 : Matrix (Fin 7) (Fin 7) ℕ := !![0,2,5,2,4,8,8;
  8,10,10,10,2,2,5;
  8,9,9,7,3,7,8;
  3,10,2,3,5,2,2;
  1,6,9,7,3,8,5;
  7,1,8,4,9,7,7;
  1,3,8,7,0,8,1]

private def mat_008 : M := castMatrix 11 7 raw_008

private theorem check_008 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_007 i k * raw_002 k j) % 11 = raw_008 i j % 11 := by
  decide +kernel

private def u_008 : Image := u_007*u_002

private theorem alias_008 : (((unitA*unitB))^3*(unitA*unitB))=u_008 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_3 alias_002

private theorem cache_008 : (u_008 : M)=mat_008 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_007 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_007 raw_002 raw_008 check_008)

private theorem pow_u_002_4 : ((unitA*unitB))^4=u_008 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_3 alias_002

private def raw_009 : Matrix (Fin 7) (Fin 7) ℕ := !![2,4,8,0,3,3,3;
  3,8,0,2,3,7,3;
  10,8,5,10,4,0,2;
  0,8,9,3,3,3,7;
  10,0,1,6,4,2,3;
  6,9,1,10,4,3,0;
  7,3,4,7,5,8,8]

private def mat_009 : M := castMatrix 11 7 raw_009

private theorem check_009 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_008 i k * raw_002 k j) % 11 = raw_009 i j % 11 := by
  decide +kernel

private def u_009 : Image := u_008*u_002

private theorem alias_009 : (((unitA*unitB))^4*(unitA*unitB))=u_009 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_4 alias_002

private theorem cache_009 : (u_009 : M)=mat_009 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_008 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_008 raw_002 raw_009 check_009)

private theorem pow_u_002_5 : ((unitA*unitB))^5=u_009 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_4 alias_002

private def raw_010 : Matrix (Fin 7) (Fin 7) ℕ := !![9,2,5,5,7,6,1;
  9,5,9,5,1,9,9;
  2,5,9,7,5,10,6;
  1,9,9,10,3,1,5;
  3,2,8,9,5,10,9;
  8,2,10,2,8,2,5;
  6,1,3,5,2,3,4]

private def mat_010 : M := castMatrix 11 7 raw_010

private theorem check_010 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_009 i k * raw_002 k j) % 11 = raw_010 i j % 11 := by
  decide +kernel

private def u_010 : Image := u_009*u_002

private theorem alias_010 : (((unitA*unitB))^5*(unitA*unitB))=u_010 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_5 alias_002

private theorem cache_010 : (u_010 : M)=mat_010 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_009 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_009 raw_002 raw_010 check_010)

private theorem pow_u_002_6 : ((unitA*unitB))^6=u_010 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_5 alias_002

private def raw_011 : Matrix (Fin 7) (Fin 7) ℕ := !![1,0,0,0,0,0,0;
  0,1,0,0,0,0,0;
  0,0,1,0,0,0,0;
  0,0,0,1,0,0,0;
  0,0,0,0,1,0,0;
  0,0,0,0,0,1,0;
  0,0,0,0,0,0,1]

private def mat_011 : M := castMatrix 11 7 raw_011

private theorem check_011 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_010 i k * raw_002 k j) % 11 = raw_011 i j % 11 := by
  decide +kernel

private def u_011 : Image := u_010*u_002

private theorem alias_011 : (((unitA*unitB))^6*(unitA*unitB))=u_011 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_6 alias_002

private theorem cache_011 : (u_011 : M)=mat_011 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_010 cache_002).trans
    (mul_eq_of_mod_dot 11 7 raw_010 raw_002 raw_011 check_011)

private theorem pow_u_002_7 : ((unitA*unitB))^7=u_011 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_002_6 alias_002

private theorem pow_u_005_1 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^1=u_005 := (pow_one _).trans alias_005

private def raw_012 : Matrix (Fin 7) (Fin 7) ℕ := !![9,3,1,6,3,6,7;
  1,4,3,2,0,0,9;
  1,4,4,2,2,2,0;
  3,0,3,1,4,4,7;
  8,10,5,9,9,3,2;
  10,7,5,3,0,1,2;
  3,8,2,8,10,10,1]

private def mat_012 : M := castMatrix 11 7 raw_012

private theorem check_012 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_005 i k * raw_005 k j) % 11 = raw_012 i j % 11 := by
  decide +kernel

private def u_012 : Image := u_005*u_005

private theorem alias_012 : (((((unitA*unitB)*unitA)*(unitB)⁻¹))^1*(((unitA*unitB)*unitA)*(unitB)⁻¹))=u_012 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_1 alias_005

private theorem cache_012 : (u_012 : M)=mat_012 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_005 cache_005).trans
    (mul_eq_of_mod_dot 11 7 raw_005 raw_005 raw_012 check_012)

private theorem pow_u_005_2 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^2=u_012 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_1 alias_005

private def raw_013 : Matrix (Fin 7) (Fin 7) ℕ := !![1,3,4,0,7,3,4;
  6,9,3,8,5,1,4;
  9,8,9,1,8,5,9;
  9,10,0,4,0,8,9;
  8,1,0,7,1,6,2;
  2,1,2,7,9,4,0;
  3,8,1,8,10,9,1]

private def mat_013 : M := castMatrix 11 7 raw_013

private theorem check_013 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_012 i k * raw_005 k j) % 11 = raw_013 i j % 11 := by
  decide +kernel

private def u_013 : Image := u_012*u_005

private theorem alias_013 : (((((unitA*unitB)*unitA)*(unitB)⁻¹))^2*(((unitA*unitB)*unitA)*(unitB)⁻¹))=u_013 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_2 alias_005

private theorem cache_013 : (u_013 : M)=mat_013 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_012 cache_005).trans
    (mul_eq_of_mod_dot 11 7 raw_012 raw_005 raw_013 check_013)

private theorem pow_u_005_3 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^3=u_013 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_2 alias_005

private def raw_014 : Matrix (Fin 7) (Fin 7) ℕ := !![5,6,4,5,6,4,1;
  5,6,7,7,10,5,5;
  6,3,8,3,5,3,6;
  4,3,8,6,6,0,7;
  4,8,6,0,4,8,6;
  10,5,5,7,5,4,6;
  6,8,0,8,7,5,7]

private def mat_014 : M := castMatrix 11 7 raw_014

private theorem check_014 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_002 i k * raw_013 k j) % 11 = raw_014 i j % 11 := by
  decide +kernel

private def u_014 : Image := u_002*u_013

private theorem alias_014 : ((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3)=u_014 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_002 pow_u_005_3

private theorem cache_014 : (u_014 : M)=mat_014 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_002 cache_013).trans
    (mul_eq_of_mod_dot 11 7 raw_002 raw_013 raw_014 check_014)

private theorem pow_u_014_1 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^1=u_014 := (pow_one _).trans alias_014

private def raw_015 : Matrix (Fin 7) (Fin 7) ℕ := !![4,4,3,2,4,10,7;
  3,0,6,7,3,9,9;
  4,3,2,8,3,2,4;
  8,1,9,3,5,6,7;
  8,1,8,0,1,3,7;
  9,3,1,9,6,1,1;
  2,3,2,5,2,10,3]

private def mat_015 : M := castMatrix 11 7 raw_015

private theorem check_015 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_014 i k * raw_014 k j) % 11 = raw_015 i j % 11 := by
  decide +kernel

private def u_015 : Image := u_014*u_014

private theorem alias_015 : ((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^1*((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))=u_015 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_1 alias_014

private theorem cache_015 : (u_015 : M)=mat_015 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_014 cache_014).trans
    (mul_eq_of_mod_dot 11 7 raw_014 raw_014 raw_015 check_015)

private theorem pow_u_014_2 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^2=u_015 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_1 alias_014

private def raw_016 : Matrix (Fin 7) (Fin 7) ℕ := !![4,3,4,8,8,9,2;
  4,0,3,1,1,3,3;
  3,6,2,9,8,1,2;
  2,7,8,3,0,9,5;
  4,3,3,5,1,6,2;
  10,9,2,6,3,1,10;
  7,9,4,7,7,1,3]

private def mat_016 : M := castMatrix 11 7 raw_016

private theorem check_016 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_015 i k * raw_014 k j) % 11 = raw_016 i j % 11 := by
  decide +kernel

private def u_016 : Image := u_015*u_014

private theorem alias_016 : ((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^2*((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))=u_016 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_2 alias_014

private theorem cache_016 : (u_016 : M)=mat_016 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_015 cache_014).trans
    (mul_eq_of_mod_dot 11 7 raw_015 raw_014 raw_016 check_016)

private theorem pow_u_014_3 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^3=u_016 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_2 alias_014

private def raw_017 : Matrix (Fin 7) (Fin 7) ℕ := !![5,5,6,4,4,10,6;
  6,6,3,3,8,5,8;
  4,7,8,8,6,5,0;
  5,7,3,6,0,7,8;
  6,10,5,6,4,5,7;
  4,5,3,0,8,4,5;
  1,5,6,7,6,6,7]

private def mat_017 : M := castMatrix 11 7 raw_017

private theorem check_017 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_016 i k * raw_014 k j) % 11 = raw_017 i j % 11 := by
  decide +kernel

private def u_017 : Image := u_016*u_014

private theorem alias_017 : ((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^3*((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))=u_017 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_3 alias_014

private theorem cache_017 : (u_017 : M)=mat_017 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_016 cache_014).trans
    (mul_eq_of_mod_dot 11 7 raw_016 raw_014 raw_017 check_017)

private theorem pow_u_014_4 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^4=u_017 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_3 alias_014

private def raw_018 : Matrix (Fin 7) (Fin 7) ℕ := !![1,0,0,0,0,0,0;
  0,1,0,0,0,0,0;
  0,0,1,0,0,0,0;
  0,0,0,1,0,0,0;
  0,0,0,0,1,0,0;
  0,0,0,0,0,1,0;
  0,0,0,0,0,0,1]

private def mat_018 : M := castMatrix 11 7 raw_018

private theorem check_018 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_017 i k * raw_014 k j) % 11 = raw_018 i j % 11 := by
  decide +kernel

private def u_018 : Image := u_017*u_014

private theorem alias_018 : ((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^4*((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))=u_018 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_4 alias_014

private theorem cache_018 : (u_018 : M)=mat_018 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_017 cache_014).trans
    (mul_eq_of_mod_dot 11 7 raw_017 raw_014 raw_018 check_018)

private theorem pow_u_014_5 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^5=u_018 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_014_4 alias_014

private def raw_019 : Matrix (Fin 7) (Fin 7) ℕ := !![10,6,0,4,7,0,3;
  5,4,5,6,8,0,0;
  4,3,0,4,4,8,10;
  5,2,6,8,4,4,7;
  2,2,6,6,6,1,4;
  6,2,3,7,6,4,4;
  2,7,7,9,2,5,3]

private def mat_019 : M := castMatrix 11 7 raw_019

private theorem check_019 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_013 i k * raw_005 k j) % 11 = raw_019 i j % 11 := by
  decide +kernel

private def u_019 : Image := u_013*u_005

private theorem alias_019 : (((((unitA*unitB)*unitA)*(unitB)⁻¹))^3*(((unitA*unitB)*unitA)*(unitB)⁻¹))=u_019 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_3 alias_005

private theorem cache_019 : (u_019 : M)=mat_019 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_013 cache_005).trans
    (mul_eq_of_mod_dot 11 7 raw_013 raw_005 raw_019 check_019)

private theorem pow_u_005_4 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^4=u_019 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_3 alias_005

private def raw_020 : Matrix (Fin 7) (Fin 7) ℕ := !![4,0,7,3,4,1,3;
  9,1,8,5,9,9,8;
  0,7,1,6,2,8,1;
  1,8,10,9,1,3,8;
  3,8,5,1,4,6,9;
  0,4,0,8,9,9,10;
  2,7,9,4,0,2,1]

private def mat_020 : M := castMatrix 11 7 raw_020

private theorem check_020 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_019 i k * raw_005 k j) % 11 = raw_020 i j % 11 := by
  decide +kernel

private def u_020 : Image := u_019*u_005

private theorem alias_020 : (((((unitA*unitB)*unitA)*(unitB)⁻¹))^4*(((unitA*unitB)*unitA)*(unitB)⁻¹))=u_020 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_4 alias_005

private theorem cache_020 : (u_020 : M)=mat_020 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_019 cache_005).trans
    (mul_eq_of_mod_dot 11 7 raw_019 raw_005 raw_020 check_020)

private theorem pow_u_005_5 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^5=u_020 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_4 alias_005

private def raw_021 : Matrix (Fin 7) (Fin 7) ℕ := !![8,5,4,9,7,6,4;
  4,10,7,5,0,0,8;
  6,2,6,9,10,6,7;
  5,6,3,4,0,6,0;
  4,5,5,2,4,8,4;
  4,4,4,8,3,0,1;
  2,9,9,7,5,4,3]

private def mat_021 : M := castMatrix 11 7 raw_021

private theorem check_021 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_020 i k * raw_005 k j) % 11 = raw_021 i j % 11 := by
  decide +kernel

private def u_021 : Image := u_020*u_005

private theorem alias_021 : (((((unitA*unitB)*unitA)*(unitB)⁻¹))^5*(((unitA*unitB)*unitA)*(unitB)⁻¹))=u_021 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_5 alias_005

private theorem cache_021 : (u_021 : M)=mat_021 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_020 cache_005).trans
    (mul_eq_of_mod_dot 11 7 raw_020 raw_005 raw_021 check_021)

private theorem pow_u_005_6 : ((((unitA*unitB)*unitA)*(unitB)⁻¹))^6=u_021 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_005_5 alias_005

private def raw_022 : Matrix (Fin 7) (Fin 7) ℕ := !![1,10,3,9,10,9,6;
  5,9,4,9,6,6,1;
  9,3,6,9,10,3,9;
  5,9,10,6,9,2,9;
  9,3,8,2,9,10,6;
  4,9,5,5,1,9,5;
  5,6,9,10,3,8,4]

private def mat_022 : M := castMatrix 11 7 raw_022

private theorem check_022 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawA i k * raw_001 k j) % 11 = raw_022 i j % 11 := by
  decide +kernel

private def u_022 : Image := unitA*u_001

private theorem alias_022 : (unitA*(unitB)⁻¹)=u_022 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_A alias_001

private theorem cache_022 : (u_022 : M)=mat_022 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_A cache_001).trans
    (mul_eq_of_mod_dot 11 7 rawA raw_001 raw_022 check_022)

private theorem pow_u_022_1 : ((unitA*(unitB)⁻¹))^1=u_022 := (pow_one _).trans alias_022

private def raw_023 : Matrix (Fin 7) (Fin 7) ℕ := !![4,7,0,8,1,6,0;
  5,5,10,4,2,9,6;
  6,8,0,0,6,4,6;
  7,6,4,7,5,2,8;
  4,4,8,1,7,3,0;
  2,9,6,3,2,4,7;
  3,7,7,7,5,9,6]

private def mat_023 : M := castMatrix 11 7 raw_023

private theorem check_023 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_022 i k * raw_022 k j) % 11 = raw_023 i j % 11 := by
  decide +kernel

private def u_023 : Image := u_022*u_022

private theorem alias_023 : (((unitA*(unitB)⁻¹))^1*(unitA*(unitB)⁻¹))=u_023 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_022_1 alias_022

private theorem cache_023 : (u_023 : M)=mat_023 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_022 cache_022).trans
    (mul_eq_of_mod_dot 11 7 raw_022 raw_022 raw_023 check_023)

private theorem pow_u_022_2 : ((unitA*(unitB)⁻¹))^2=u_023 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_022_1 alias_022

private def raw_024 : Matrix (Fin 7) (Fin 7) ℕ := !![5,4,6,7,6,10,6;
  8,8,6,8,6,6,8;
  0,8,7,5,4,5,8;
  8,5,5,0,7,4,8;
  7,5,6,4,10,6,6;
  5,0,4,8,5,7,8;
  4,7,10,5,6,6,6]

private def mat_024 : M := castMatrix 11 7 raw_024

private theorem check_024 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_002 i k * raw_021 k j) % 11 = raw_024 i j % 11 := by
  decide +kernel

private def u_024 : Image := u_002*u_021

private theorem alias_024 : ((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)=u_024 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_002 pow_u_005_6

private theorem cache_024 : (u_024 : M)=mat_024 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_002 cache_021).trans
    (mul_eq_of_mod_dot 11 7 raw_002 raw_021 raw_024 check_024)

private def raw_025 : Matrix (Fin 7) (Fin 7) ℕ := !![10,9,9,3,0,9,10;
  4,8,6,10,9,6,8;
  3,9,10,7,3,7,10;
  8,5,5,9,1,5,0;
  2,0,3,8,5,7,2;
  4,7,3,6,5,7,2;
  10,8,4,5,6,8,9]

private def mat_025 : M := castMatrix 11 7 raw_025

private theorem check_025 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_024 i k * rawA k j) % 11 = raw_025 i j % 11 := by
  decide +kernel

private def u_025 : Image := u_024*unitA

private theorem alias_025 : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)=u_025 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_024 alias_A

private theorem cache_025 : (u_025 : M)=mat_025 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_024 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_024 rawA raw_025 check_025)

private def raw_026 : Matrix (Fin 7) (Fin 7) ℕ := !![6,7,2,3,10,0,10;
  2,8,7,3,3,3,0;
  10,7,3,0,6,2,10;
  1,4,0,9,1,8,5;
  4,5,3,3,4,3,4;
  3,8,3,7,0,3,2;
  0,3,8,8,9,4,8]

private def mat_026 : M := castMatrix 11 7 raw_026

private theorem check_026 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_025 i k * rawB k j) % 11 = raw_026 i j % 11 := by
  decide +kernel

private def u_026 : Image := u_025*unitB

private theorem alias_026 : ((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)=u_026 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_025 alias_B

private theorem cache_026 : (u_026 : M)=mat_026 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_025 cache_B).trans
    (mul_eq_of_mod_dot 11 7 raw_025 rawB raw_026 check_026)

private def raw_027 : Matrix (Fin 7) (Fin 7) ℕ := !![9,5,7,6,4,4,8;
  10,7,3,3,9,7,10;
  9,5,10,6,8,8,4;
  0,2,3,10,6,6,6;
  10,3,10,0,9,9,9;
  9,3,9,6,0,4,8;
  3,1,7,2,3,5,5]

private def mat_027 : M := castMatrix 11 7 raw_027

private theorem check_027 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_026 i k * rawA k j) % 11 = raw_027 i j % 11 := by
  decide +kernel

private def u_027 : Image := u_026*unitA

private theorem alias_027 : (((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)=u_027 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_026 alias_A

private theorem cache_027 : (u_027 : M)=mat_027 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_026 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_026 rawA raw_027 check_027)

private def raw_028 : Matrix (Fin 7) (Fin 7) ℕ := !![8,2,9,10,6,9,3;
  2,1,8,3,7,6,5;
  7,2,5,5,10,6,2;
  1,5,2,9,2,6,2;
  5,5,1,9,5,4,9;
  3,9,10,9,6,1,10;
  5,2,1,8,2,2,8]

private def mat_028 : M := castMatrix 11 7 raw_028

private theorem check_028 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_027 i k * rawB k j) % 11 = raw_028 i j % 11 := by
  decide +kernel

private def u_028 : Image := u_027*unitB

private theorem alias_028 : ((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)=u_028 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_027 alias_B

private theorem cache_028 : (u_028 : M)=mat_028 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_027 cache_B).trans
    (mul_eq_of_mod_dot 11 7 raw_027 rawB raw_028 check_028)

private def raw_029 : Matrix (Fin 7) (Fin 7) ℕ := !![8,5,7,9,4,5,7;
  5,9,6,2,10,6,7;
  7,6,5,9,4,8,4;
  9,2,9,4,5,4,3;
  4,10,4,5,0,0,3;
  5,6,8,4,0,5,0;
  7,7,4,3,3,0,1]

private def mat_029 : M := castMatrix 11 7 raw_029

private theorem check_029 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_028 i k * raw_023 k j) % 11 = raw_029 i j % 11 := by
  decide +kernel

private def u_029 : Image := u_028*u_023

private theorem alias_029 : (((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2)=u_029 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_028 pow_u_022_2

private theorem cache_029 : (u_029 : M)=mat_029 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_028 cache_023).trans
    (mul_eq_of_mod_dot 11 7 raw_028 raw_023 raw_029 check_029)

private theorem pow_u_029_1 : ((((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2))^1=u_029 := (pow_one _).trans alias_029

private def raw_030 : Matrix (Fin 7) (Fin 7) ℕ := !![1,0,0,0,0,0,0;
  0,1,0,0,0,0,0;
  0,0,1,0,0,0,0;
  0,0,0,1,0,0,0;
  0,0,0,0,1,0,0;
  0,0,0,0,0,1,0;
  0,0,0,0,0,0,1]

private def mat_030 : M := castMatrix 11 7 raw_030

private theorem check_030 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_029 i k * raw_029 k j) % 11 = raw_030 i j % 11 := by
  decide +kernel

private def u_030 : Image := u_029*u_029

private theorem alias_030 : (((((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2))^1*(((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2))=u_030 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_029_1 alias_029

private theorem cache_030 : (u_030 : M)=mat_030 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_029 cache_029).trans
    (mul_eq_of_mod_dot 11 7 raw_029 raw_029 raw_030 check_030)

private theorem pow_u_029_2 : ((((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2))^2=u_030 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_029_1 alias_029

private theorem one_product_seventh : u_011=1 := by
  apply Units.ext
  exact cache_011.trans (by decide +kernel : mat_011=(1 : M))

theorem product_seventh : ((unitA*unitB))^7=1 := pow_u_002_7.trans one_product_seventh

private theorem one_fourth_fifth : u_018=1 := by
  apply Units.ext
  exact cache_018.trans (by decide +kernel : mat_018=(1 : M))

theorem fourth_fifth : (((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^3))^5=1 := pow_u_014_5.trans one_fourth_fifth

private theorem one_last_square : u_030=1 := by
  apply Units.ext
  exact cache_030.trans (by decide +kernel : mat_030=(1 : M))

theorem last_square : ((((((((unitA*unitB)*((((unitA*unitB)*unitA)*(unitB)⁻¹))^6)*unitA)*unitB)*unitA)*unitB)*((unitA*(unitB)⁻¹))^2))^2=1 := pow_u_029_2.trans one_last_square

private theorem pow_unitB_1 : (unitB)^1=unitB := (pow_one _).trans alias_B

private def raw_031 : Matrix (Fin 7) (Fin 7) ℕ := !![5,10,5,2,7,3,3;
  7,4,10,3,4,9,4;
  1,10,8,3,7,0,3;
  8,0,9,6,2,4,3;
  5,3,1,1,10,2,9;
  8,3,2,2,7,3,4;
  2,8,1,9,3,5,9]

private def mat_031 : M := castMatrix 11 7 raw_031

private theorem check_031 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawB i k * rawB k j) % 11 = raw_031 i j % 11 := by
  decide +kernel

private def u_031 : Image := unitB*unitB

private theorem alias_031 : ((unitB)^1*unitB)=u_031 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_unitB_1 alias_B

private theorem cache_031 : (u_031 : M)=mat_031 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_B cache_B).trans
    (mul_eq_of_mod_dot 11 7 rawB rawB raw_031 check_031)

private theorem pow_unitB_2 : (unitB)^2=u_031 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_unitB_1 alias_B

private def raw_032 : Matrix (Fin 7) (Fin 7) ℕ := !![1,5,9,5,9,4,5;
  10,9,3,9,3,9,6;
  3,4,6,10,8,5,9;
  9,9,9,6,2,5,10;
  10,6,10,9,9,1,3;
  9,6,3,2,10,9,8;
  6,1,9,9,6,5,4]

private def mat_032 : M := castMatrix 11 7 raw_032

private theorem check_032 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawB i k * rawA k j) % 11 = raw_032 i j % 11 := by
  decide +kernel

private def u_032 : Image := unitB*unitA

private theorem alias_032 : (unitB*unitA)=u_032 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_B alias_A

private theorem cache_032 : (u_032 : M)=mat_032 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_B cache_A).trans
    (mul_eq_of_mod_dot 11 7 rawB rawA raw_032 check_032)

private def raw_033 : Matrix (Fin 7) (Fin 7) ℕ := !![2,4,7,3,1,3,1;
  8,5,3,1,4,5,9;
  5,9,6,3,5,10,0;
  9,3,2,1,9,0,10;
  0,3,7,2,8,5,9;
  3,1,6,4,5,9,3;
  7,6,4,7,3,6,2]

private def mat_033 : M := castMatrix 11 7 raw_033

private theorem check_033 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_032 i k * rawB k j) % 11 = raw_033 i j % 11 := by
  decide +kernel

private def u_033 : Image := u_032*unitB

private theorem alias_033 : ((unitB*unitA)*unitB)=u_033 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_032 alias_B

private theorem cache_033 : (u_033 : M)=mat_033 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_032 cache_B).trans
    (mul_eq_of_mod_dot 11 7 raw_032 rawB raw_033 check_033)

private def raw_034 : Matrix (Fin 7) (Fin 7) ℕ := !![4,5,6,7,4,2,3;
  7,5,8,6,4,9,7;
  0,10,0,4,8,6,7;
  8,4,0,7,1,3,7;
  1,2,6,5,7,2,5;
  6,9,4,2,3,4,9;
  0,6,6,8,0,7,6]

private def mat_034 : M := castMatrix 11 7 raw_034

private theorem check_034 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_033 i k * rawA k j) % 11 = raw_034 i j % 11 := by
  decide +kernel

private def u_034 : Image := u_033*unitA

private theorem alias_034 : (((unitB*unitA)*unitB)*unitA)=u_034 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_033 alias_A

private theorem cache_034 : (u_034 : M)=mat_034 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_033 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_033 rawA raw_034 check_034)

private def raw_035 : Matrix (Fin 7) (Fin 7) ℕ := !![5,8,5,8,2,4,10;
  1,1,1,9,8,6,9;
  6,6,9,5,4,10,2;
  2,10,3,8,6,2,2;
  5,2,2,2,1,9,6;
  2,9,3,1,8,5,9;
  4,10,2,9,6,5,5]

private def mat_035 : M := castMatrix 11 7 raw_035

private theorem check_035 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_034 i k * raw_031 k j) % 11 = raw_035 i j % 11 := by
  decide +kernel

private def u_035 : Image := u_034*u_031

private theorem alias_035 : ((((unitB*unitA)*unitB)*unitA)*(unitB)^2)=u_035 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_034 pow_unitB_2

private theorem cache_035 : (u_035 : M)=mat_035 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_034 cache_031).trans
    (mul_eq_of_mod_dot 11 7 raw_034 raw_031 raw_035 check_035)

private def raw_036 : Matrix (Fin 7) (Fin 7) ℕ := !![5,1,6,2,5,2,4;
  8,1,6,10,2,9,10;
  5,1,9,3,2,3,2;
  8,9,5,8,2,1,9;
  2,8,4,6,1,8,6;
  4,6,10,2,9,5,5;
  10,9,2,2,6,9,5]

private def mat_036 : M := castMatrix 11 7 raw_036

private theorem check_036 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_035 i k * raw_036 k j) % 11 = (1 : Matrix (Fin 7) (Fin 7) ℕ) i j % 11 := by
  decide +kernel

private def u_036 : Image := u_035⁻¹

private theorem alias_036 : (((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹=u_036 := congrArg (fun x : Image => x⁻¹) alias_035

private theorem cache_036 : (u_036 : M)=mat_036 := by
  have hr : (u_035 : M)*mat_036=1 :=
    (congrArg (fun x : M => x*mat_036) cache_035).trans
      ((mul_eq_of_mod_dot 11 7 raw_035 raw_036 1 check_036).trans (castMatrix_one 11 7))
  exact UnitsInverseValueUniqueness.inverse_val_eq_of_mul_eq_one _ _ hr

private def raw_037 : Matrix (Fin 7) (Fin 7) ℕ := !![3,3,10,8,1,9,1;
  9,1,0,4,0,8,9;
  1,8,7,0,4,3,4;
  3,1,0,4,1,5,9;
  5,9,3,3,5,10,7;
  2,10,9,7,2,4,0;
  2,8,9,10,8,6,2]

private def mat_037 : M := castMatrix 11 7 raw_037

private theorem check_037 : ∀ i j : Fin 7,
    (∑ k : Fin 7, rawA i k * raw_036 k j) % 11 = raw_037 i j % 11 := by
  decide +kernel

private def u_037 : Image := unitA*u_036

private theorem alias_037 : (unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)=u_037 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_A alias_036

private theorem cache_037 : (u_037 : M)=mat_037 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_A cache_036).trans
    (mul_eq_of_mod_dot 11 7 rawA raw_036 raw_037 check_037)

private def raw_038 : Matrix (Fin 7) (Fin 7) ℕ := !![1,9,8,1,2,5,10;
  4,7,4,8,2,4,10;
  7,7,3,9,8,3,2;
  4,3,1,3,0,1,3;
  3,2,8,2,6,9,1;
  9,3,0,6,4,8,2;
  4,3,1,2,3,5,6]

private def mat_038 : M := castMatrix 11 7 raw_038

private theorem check_038 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_037 i k * rawA k j) % 11 = raw_038 i j % 11 := by
  decide +kernel

private def u_038 : Image := u_037*unitA

private theorem alias_038 : ((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)=u_038 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_037 alias_A

private theorem cache_038 : (u_038 : M)=mat_038 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_037 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_037 rawA raw_038 check_038)

private def raw_039 : Matrix (Fin 7) (Fin 7) ℕ := !![3,4,7,5,5,2,7;
  4,8,2,2,2,4,5;
  0,3,4,1,4,6,0;
  5,0,6,6,3,4,0;
  0,10,4,7,7,3,3;
  5,4,3,5,4,9,4;
  5,7,5,2,6,9,1]

private def mat_039 : M := castMatrix 11 7 raw_039

private theorem check_039 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_038 i k * raw_035 k j) % 11 = raw_039 i j % 11 := by
  decide +kernel

private def u_039 : Image := u_038*u_035

private theorem alias_039 : (((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2))=u_039 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_038 alias_035

private theorem cache_039 : (u_039 : M)=mat_039 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_038 cache_035).trans
    (mul_eq_of_mod_dot 11 7 raw_038 raw_035 raw_039 check_039)

private theorem pow_u_039_1 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^1=u_039 := (pow_one _).trans alias_039

private def raw_040 : Matrix (Fin 7) (Fin 7) ℕ := !![7,7,5,9,8,4,5;
  0,3,10,6,0,4,7;
  3,1,7,8,0,7,7;
  10,7,9,9,5,5,5;
  6,8,9,4,4,2,9;
  0,0,5,4,5,6,8;
  4,7,5,2,6,8,4]

private def mat_040 : M := castMatrix 11 7 raw_040

private theorem check_040 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_039 i k * raw_039 k j) % 11 = raw_040 i j % 11 := by
  decide +kernel

private def u_040 : Image := u_039*u_039

private theorem alias_040 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^1*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_040 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_1 alias_039

private theorem cache_040 : (u_040 : M)=mat_040 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_039 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_039 raw_039 raw_040 check_040)

private theorem pow_u_039_2 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^2=u_040 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_1 alias_039

private def raw_041 : Matrix (Fin 7) (Fin 7) ℕ := !![7,10,8,7,0,4,8;
  9,9,8,9,1,8,5;
  2,8,1,0,7,1,6;
  10,8,3,10,3,1,2;
  4,6,9,3,8,5,1;
  2,2,1,0,7,0,3;
  0,9,10,9,4,2,7]

private def mat_041 : M := castMatrix 11 7 raw_041

private theorem check_041 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_040 i k * raw_039 k j) % 11 = raw_041 i j % 11 := by
  decide +kernel

private def u_041 : Image := u_040*u_039

private theorem alias_041 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^2*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_041 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_2 alias_039

private theorem cache_041 : (u_041 : M)=mat_041 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_040 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_040 raw_039 raw_041 check_041)

private theorem pow_u_039_3 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^3=u_041 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_2 alias_039

private def raw_042 : Matrix (Fin 7) (Fin 7) ℕ := !![2,6,8,9,7,7,2;
  8,0,0,6,4,5,5;
  7,4,7,5,9,5,8;
  6,7,7,5,2,3,4;
  4,0,3,10,5,0,4;
  7,8,10,4,8,0,4;
  5,1,4,2,9,5,6]

private def mat_042 : M := castMatrix 11 7 raw_042

private theorem check_042 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_041 i k * raw_039 k j) % 11 = raw_042 i j % 11 := by
  decide +kernel

private def u_042 : Image := u_041*u_039

private theorem alias_042 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^3*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_042 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_3 alias_039

private theorem cache_042 : (u_042 : M)=mat_042 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_041 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_041 raw_039 raw_042 check_042)

private theorem pow_u_039_4 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^4=u_042 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_3 alias_039

private def raw_043 : Matrix (Fin 7) (Fin 7) ℕ := !![10,5,6,7,5,5,7;
  5,6,5,7,4,10,5;
  6,5,8,8,8,5,3;
  7,7,8,8,5,6,0;
  5,4,8,5,0,7,3;
  5,10,5,6,7,6,7;
  7,5,3,0,3,7,5]

private def mat_043 : M := castMatrix 11 7 raw_043

private theorem check_043 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_042 i k * raw_039 k j) % 11 = raw_043 i j % 11 := by
  decide +kernel

private def u_043 : Image := u_042*u_039

private theorem alias_043 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^4*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_043 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_4 alias_039

private theorem cache_043 : (u_043 : M)=mat_043 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_042 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_042 raw_039 raw_043 check_043)

private theorem pow_u_039_5 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5=u_043 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_4 alias_039

private def raw_044 : Matrix (Fin 7) (Fin 7) ℕ := !![2,8,7,6,4,7,5;
  6,0,4,7,0,8,1;
  8,0,7,7,3,10,4;
  9,6,5,5,10,4,2;
  7,4,9,2,5,8,9;
  7,5,5,3,0,0,5;
  2,5,8,4,4,4,6]

private def mat_044 : M := castMatrix 11 7 raw_044

private theorem check_044 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_043 i k * raw_039 k j) % 11 = raw_044 i j % 11 := by
  decide +kernel

private def u_044 : Image := u_043*u_039

private theorem alias_044 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_044 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_5 alias_039

private theorem cache_044 : (u_044 : M)=mat_044 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_043 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_043 raw_039 raw_044 check_044)

private theorem pow_u_039_6 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^6=u_044 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_5 alias_039

private def raw_045 : Matrix (Fin 7) (Fin 7) ℕ := !![7,9,2,10,4,2,0;
  10,9,8,8,6,2,9;
  8,8,1,3,9,1,10;
  7,9,0,10,3,0,9;
  0,1,7,3,8,7,4;
  4,8,1,1,5,0,2;
  8,5,6,2,1,3,7]

private def mat_045 : M := castMatrix 11 7 raw_045

private theorem check_045 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_044 i k * raw_039 k j) % 11 = raw_045 i j % 11 := by
  decide +kernel

private def u_045 : Image := u_044*u_039

private theorem alias_045 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^6*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_045 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_6 alias_039

private theorem cache_045 : (u_045 : M)=mat_045 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_044 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_044 raw_039 raw_045 check_045)

private theorem pow_u_039_7 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^7=u_045 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_6 alias_039

private def raw_046 : Matrix (Fin 7) (Fin 7) ℕ := !![7,0,3,10,6,0,4;
  7,3,1,7,8,0,7;
  5,10,7,9,9,5,5;
  9,6,8,9,4,4,2;
  8,0,0,5,4,5,6;
  4,4,7,5,2,6,8;
  5,7,7,5,9,8,4]

private def mat_046 : M := castMatrix 11 7 raw_046

private theorem check_046 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_045 i k * raw_039 k j) % 11 = raw_046 i j % 11 := by
  decide +kernel

private def u_046 : Image := u_045*u_039

private theorem alias_046 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^7*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_046 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_7 alias_039

private theorem cache_046 : (u_046 : M)=mat_046 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_045 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_045 raw_039 raw_046 check_046)

private theorem pow_u_039_8 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^8=u_046 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_7 alias_039

private def raw_047 : Matrix (Fin 7) (Fin 7) ℕ := !![3,4,0,5,0,5,5;
  4,8,3,0,10,4,7;
  7,2,4,6,4,3,5;
  5,2,1,6,7,5,2;
  5,2,4,3,7,4,6;
  2,4,6,4,3,9,9;
  7,5,0,0,3,4,1]

private def mat_047 : M := castMatrix 11 7 raw_047

private theorem check_047 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_046 i k * raw_039 k j) % 11 = raw_047 i j % 11 := by
  decide +kernel

private def u_047 : Image := u_046*u_039

private theorem alias_047 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^8*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_047 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_8 alias_039

private theorem cache_047 : (u_047 : M)=mat_047 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_046 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_046 raw_039 raw_047 check_047)

private theorem pow_u_039_9 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^9=u_047 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_8 alias_039

private def raw_048 : Matrix (Fin 7) (Fin 7) ℕ := !![1,0,0,0,0,0,0;
  0,1,0,0,0,0,0;
  0,0,1,0,0,0,0;
  0,0,0,1,0,0,0;
  0,0,0,0,1,0,0;
  0,0,0,0,0,1,0;
  0,0,0,0,0,0,1]

private def mat_048 : M := castMatrix 11 7 raw_048

private theorem check_048 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_047 i k * raw_039 k j) % 11 = raw_048 i j % 11 := by
  decide +kernel

private def u_048 : Image := u_047*u_039

private theorem alias_048 : (((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^9*(((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))=u_048 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_9 alias_039

private theorem cache_048 : (u_048 : M)=mat_048 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_047 cache_039).trans
    (mul_eq_of_mod_dot 11 7 raw_047 raw_039 raw_048 check_048)

private theorem pow_u_039_10 : ((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^10=u_048 := by
  rw [pow_succ]
  exact congrArg₂ (fun x y : Image => x*y) pow_u_039_9 alias_039

def conjugator : Image := unitB*unitA*unitB*unitA*unitB^2

def rotation : Image := unitA*(conjugator⁻¹*unitA*conjugator)

private theorem one_rotation_tenth : u_048=1 := by
  apply Units.ext
  exact cache_048.trans (by decide +kernel : mat_048=(1 : M))

theorem rotation_tenth : rotation^10=1 := by
  simpa only [rotation,conjugator,mul_assoc] using pow_u_039_10.trans one_rotation_tenth

private def raw_049 : Matrix (Fin 7) (Fin 7) ℕ := !![9,2,5,5,7,6,1;
  9,5,9,5,1,9,9;
  2,5,9,7,5,10,6;
  1,9,9,10,3,1,5;
  3,2,8,9,5,10,9;
  8,2,10,2,8,2,5;
  6,1,3,5,2,3,4]

private def mat_049 : M := castMatrix 11 7 raw_049

private theorem check_049 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_031 i k * rawA k j) % 11 = raw_049 i j % 11 := by
  decide +kernel

private def u_049 : Image := u_031*unitA

private theorem alias_049 : ((unitB)^2*unitA)=u_049 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_unitB_2 alias_A

private theorem cache_049 : (u_049 : M)=mat_049 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_031 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_031 rawA raw_049 check_049)

private def raw_050 : Matrix (Fin 7) (Fin 7) ℕ := !![5,2,4,1,9,4,1;
  2,1,4,6,7,9,10;
  4,4,0,9,0,9,4;
  1,6,9,9,7,7,1;
  9,7,0,7,2,0,4;
  4,9,9,7,0,0,7;
  1,10,4,1,4,7,4]

private def mat_050 : M := castMatrix 11 7 raw_050

private theorem check_050 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_049 i k * rawB k j) % 11 = raw_050 i j % 11 := by
  decide +kernel

private def u_050 : Image := u_049*unitB

private theorem alias_050 : (((unitB)^2*unitA)*unitB)=u_050 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_049 alias_B

private theorem cache_050 : (u_050 : M)=mat_050 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_049 cache_B).trans
    (mul_eq_of_mod_dot 11 7 raw_049 rawB raw_050 check_050)

private def raw_051 : Matrix (Fin 7) (Fin 7) ℕ := !![6,10,7,5,2,8,3;
  0,3,2,2,1,0,7;
  9,4,0,2,1,2,7;
  7,3,4,1,3,4,0;
  3,6,2,2,3,2,10;
  1,6,2,8,1,0,7;
  1,2,10,8,3,10,3]

private def mat_051 : M := castMatrix 11 7 raw_051

private theorem check_051 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_031 i k * raw_043 k j) % 11 = raw_051 i j % 11 := by
  decide +kernel

private def u_051 : Image := u_031*u_043

private theorem alias_051 : ((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)=u_051 := by
  exact congrArg₂ (fun x y : Image => x*y) pow_unitB_2 pow_u_039_5

private theorem cache_051 : (u_051 : M)=mat_051 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_031 cache_043).trans
    (mul_eq_of_mod_dot 11 7 raw_031 raw_043 raw_051 check_051)

private def raw_052 : Matrix (Fin 7) (Fin 7) ℕ := !![2,6,2,10,3,9,8;
  6,4,3,9,9,8,0;
  2,3,6,5,4,8,1;
  10,9,5,10,10,9,3;
  3,9,4,10,7,7,7;
  9,8,8,9,7,4,3;
  8,0,1,3,7,3,10]

private def mat_052 : M := castMatrix 11 7 raw_052

private theorem check_052 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_051 i k * rawB k j) % 11 = raw_052 i j % 11 := by
  decide +kernel

private def u_052 : Image := u_051*unitB

private theorem alias_052 : (((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB)=u_052 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_051 alias_B

private theorem cache_052 : (u_052 : M)=mat_052 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_051 cache_B).trans
    (mul_eq_of_mod_dot 11 7 raw_051 rawB raw_052 check_052)

private def raw_053 : Matrix (Fin 7) (Fin 7) ℕ := !![9,2,10,4,2,0,7;
  10,4,8,3,4,7,0;
  9,8,8,6,2,9,10;
  3,10,10,6,0,9,7;
  3,10,8,2,10,1,3;
  6,5,9,10,8,4,3;
  9,0,10,3,0,9,7]

private def mat_053 : M := castMatrix 11 7 raw_053

private theorem check_053 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_050 i k * raw_043 k j) % 11 = raw_053 i j % 11 := by
  decide +kernel

private def u_053 : Image := u_050*u_043

private theorem alias_053 : ((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)=u_053 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_050 pow_u_039_5

private theorem cache_053 : (u_053 : M)=mat_053 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_050 cache_043).trans
    (mul_eq_of_mod_dot 11 7 raw_050 raw_043 raw_053 check_053)

private def raw_054 : Matrix (Fin 7) (Fin 7) ℕ := !![8,3,9,3,1,1,10;
  3,0,3,1,4,4,7;
  9,3,1,6,3,6,7;
  3,1,6,2,2,8,9;
  1,4,3,2,0,0,9;
  1,4,6,8,0,10,9;
  10,7,7,9,9,9,0]

private def mat_054 : M := castMatrix 11 7 raw_054

private theorem check_054 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_053 i k * raw_050 k j) % 11 = raw_054 i j % 11 := by
  decide +kernel

private def u_054 : Image := u_053*u_050

private theorem alias_054 : (((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))=u_054 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_053 alias_050

private theorem cache_054 : (u_054 : M)=mat_054 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_053 cache_050).trans
    (mul_eq_of_mod_dot 11 7 raw_053 raw_050 raw_054 check_054)

private def raw_055 : Matrix (Fin 7) (Fin 7) ℕ := !![5,2,3,6,3,1,7;
  2,3,3,1,5,7,5;
  10,0,6,2,6,3,6;
  5,2,7,6,7,4,3;
  0,10,9,3,9,10,9;
  8,1,2,4,4,8,1;
  5,2,0,8,7,2,3]

private def mat_055 : M := castMatrix 11 7 raw_055

private theorem check_055 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_054 i k * rawA k j) % 11 = raw_055 i j % 11 := by
  decide +kernel

private def u_055 : Image := u_054*unitA

private theorem alias_055 : ((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)=u_055 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_054 alias_A

private theorem cache_055 : (u_055 : M)=mat_055 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_054 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_054 rawA raw_055 check_055)

private def raw_056 : Matrix (Fin 7) (Fin 7) ℕ := !![8,4,3,5,6,9,1;
  2,0,7,2,9,10,7;
  2,9,10,2,3,8,5;
  1,10,8,3,10,3,2;
  0,2,4,9,0,1,3;
  4,7,0,1,7,8,8;
  0,2,4,3,10,1,6]

private def mat_056 : M := castMatrix 11 7 raw_056

private theorem check_056 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_055 i k * raw_052 k j) % 11 = raw_056 i j % 11 := by
  decide +kernel

private def u_056 : Image := u_055*u_052

private theorem alias_056 : (((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))=u_056 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_055 alias_052

private theorem cache_056 : (u_056 : M)=mat_056 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_055 cache_052).trans
    (mul_eq_of_mod_dot 11 7 raw_055 raw_052 raw_056 check_056)

private def raw_057 : Matrix (Fin 7) (Fin 7) ℕ := !![4,2,8,1,6,8,6;
  0,10,7,4,2,9,2;
  9,3,1,5,9,2,3;
  10,8,3,2,8,1,10;
  2,10,7,3,2,0,0;
  4,8,0,3,1,7,4;
  9,1,4,5,3,0,1]

private def mat_057 : M := castMatrix 11 7 raw_057

private theorem check_057 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_056 i k * raw_043 k j) % 11 = raw_057 i j % 11 := by
  decide +kernel

private def u_057 : Image := u_056*u_043

private theorem alias_057 : ((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)=u_057 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_056 pow_u_039_5

private theorem cache_057 : (u_057 : M)=mat_057 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_056 cache_043).trans
    (mul_eq_of_mod_dot 11 7 raw_056 raw_043 raw_057 check_057)

private def raw_058 : Matrix (Fin 7) (Fin 7) ℕ := !![6,2,8,3,5,1,7;
  9,1,0,7,0,8,2;
  9,1,2,7,2,7,0;
  1,8,7,0,7,3,7;
  2,8,9,1,3,6,9;
  3,1,0,7,10,5,2;
  8,8,1,8,1,2,1]

private def mat_058 : M := castMatrix 11 7 raw_058

private theorem check_058 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_057 i k * raw_050 k j) % 11 = raw_058 i j % 11 := by
  decide +kernel

private def u_058 : Image := u_057*u_050

private theorem alias_058 : (((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))=u_058 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_057 alias_050

private theorem cache_058 : (u_058 : M)=mat_058 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_057 cache_050).trans
    (mul_eq_of_mod_dot 11 7 raw_057 raw_050 raw_058 check_058)

private def raw_059 : Matrix (Fin 7) (Fin 7) ℕ := !![9,3,2,10,2,0,1;
  0,3,7,9,3,5,2;
  3,1,6,7,6,9,8;
  4,5,7,7,3,5,2;
  9,7,4,3,1,8,1;
  8,5,3,10,7,5,2;
  6,2,5,3,5,1,0]

private def mat_059 : M := castMatrix 11 7 raw_059

private theorem check_059 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_058 i k * raw_043 k j) % 11 = raw_059 i j % 11 := by
  decide +kernel

private def u_059 : Image := u_058*u_043

private theorem alias_059 : ((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)=u_059 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_058 pow_u_039_5

private theorem cache_059 : (u_059 : M)=mat_059 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_058 cache_043).trans
    (mul_eq_of_mod_dot 11 7 raw_058 raw_043 raw_059 check_059)

private def raw_060 : Matrix (Fin 7) (Fin 7) ℕ := !![4,5,0,2,0,0,0;
  6,9,0,4,0,0,0;
  0,0,8,0,8,2,10;
  2,7,0,6,0,0,0;
  0,0,8,0,9,3,10;
  0,0,9,0,8,3,10;
  0,0,1,0,1,10,3]

private def mat_060 : M := castMatrix 11 7 raw_060

private theorem check_060 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_059 i k * rawA k j) % 11 = raw_060 i j % 11 := by
  decide +kernel

private def u_060 : Image := u_059*unitA

private theorem alias_060 : (((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitA)=u_060 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_059 alias_A

private theorem cache_060 : (u_060 : M)=mat_060 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_059 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_059 rawA raw_060 check_060)

private def raw_061 : Matrix (Fin 7) (Fin 7) ℕ := !![10,3,10,8,8,9,1;
  8,1,8,8,2,1,1;
  1,8,3,9,1,10,8;
  8,3,2,10,10,3,1;
  3,2,1,1,3,10,8;
  9,10,1,3,1,8,8;
  1,10,3,1,3,8,2]

private def mat_061 : M := castMatrix 11 7 raw_061

private theorem check_061 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_060 i k * raw_050 k j) % 11 = raw_061 i j % 11 := by
  decide +kernel

private def u_061 : Image := u_060*u_050

private theorem alias_061 : ((((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitA)*(((unitB)^2*unitA)*unitB))=u_061 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_060 alias_050

private theorem cache_061 : (u_061 : M)=mat_061 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_060 cache_050).trans
    (mul_eq_of_mod_dot 11 7 raw_060 raw_050 raw_061 check_061)

private def raw_062 : Matrix (Fin 7) (Fin 7) ℕ := !![5,2,4,5,7,7,3;
  0,10,2,8,9,1,9;
  8,1,9,7,4,3,1;
  6,9,0,8,4,2,8;
  6,9,3,6,8,1,4;
  2,3,8,10,5,4,5;
  1,0,6,2,5,3,5]

private def mat_062 : M := castMatrix 11 7 raw_062

private theorem check_062 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_061 i k * rawA k j) % 11 = raw_062 i j % 11 := by
  decide +kernel

private def u_062 : Image := u_061*unitA

private theorem alias_062 : (((((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitA)*(((unitB)^2*unitA)*unitB))*unitA)=u_062 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_061 alias_A

private theorem cache_062 : (u_062 : M)=mat_062 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_061 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_061 rawA raw_062 check_062)

private def raw_063 : Matrix (Fin 7) (Fin 7) ℕ := !![1,5,9,5,9,4,5;
  10,9,3,9,3,9,6;
  3,4,6,10,8,5,9;
  9,9,9,6,2,5,10;
  10,6,10,9,9,1,3;
  9,6,3,2,10,9,8;
  6,1,9,9,6,5,4]

private def mat_063 : M := castMatrix 11 7 raw_063

private theorem check_063 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_062 i k * raw_052 k j) % 11 = raw_063 i j % 11 := by
  decide +kernel

private def u_063 : Image := u_062*u_052

private theorem alias_063 : ((((((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitA)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))=u_063 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_062 alias_052

private theorem cache_063 : (u_063 : M)=mat_063 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_062 cache_052).trans
    (mul_eq_of_mod_dot 11 7 raw_062 raw_052 raw_063 check_063)

private def raw_064 : Matrix (Fin 7) (Fin 7) ℕ := !![5,7,1,8,5,8,2;
  10,4,10,0,3,3,8;
  5,10,8,9,1,2,1;
  2,3,3,6,1,2,9;
  7,4,7,2,10,7,3;
  3,9,0,4,2,3,5;
  3,4,3,3,9,4,9]

private def mat_064 : M := castMatrix 11 7 raw_064

private theorem check_064 : ∀ i j : Fin 7,
    (∑ k : Fin 7, raw_063 i k * rawA k j) % 11 = raw_064 i j % 11 := by
  decide +kernel

private def u_064 : Image := u_063*unitA

private theorem alias_064 : (((((((((((((((unitB)^2*unitA)*unitB)*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*(((unitB)^2*unitA)*unitB))*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitA)*(((unitB)^2*unitA)*unitB))*unitA)*(((unitB)^2*((((unitA*(((((unitB*unitA)*unitB)*unitA)*(unitB)^2))⁻¹)*unitA)*((((unitB*unitA)*unitB)*unitA)*(unitB)^2)))^5)*unitB))*unitA)=u_064 := by
  exact congrArg₂ (fun x y : Image => x*y) alias_063 alias_A

private theorem cache_064 : (u_064 : M)=mat_064 := by
  exact (congrArg₂ (fun x y : M => x*y) cache_063 cache_A).trans
    (mul_eq_of_mod_dot 11 7 raw_063 rawA raw_064 check_064)

def seeds : Fin 4 → Image := ![unitA,rotation^5,unitB^2*unitA*unitB,unitB^2*rotation^5*unitB]

def recoveryIndices : List (Fin 4) := [2,1,2,0,3,1,2,1,0,2,0,3,0]

private theorem recovered_eq : u_064=unitB := by
  apply Units.ext
  exact cache_064.trans (by decide +kernel : mat_064=matrixB)

theorem recovery_product : (recoveryIndices.map seeds).prod=unitB := by
  simpa [recoveryIndices,seeds,rotation,conjugator,mul_assoc] using
    alias_064.trans recovered_eq

theorem relatorPacket : CFSGJankoOneLiteralRepresentation.RelatorPacket unitA unitB := by
  constructor
  · apply Units.ext; exact matrixA_square
  · apply Units.ext; exact matrixB_cube
  · exact product_seventh
  · simpa only [CFSGJankoOneLiteralRepresentation.fourthWord,pow_one] using fourth_fifth
  · simpa only [CFSGJankoOnePresentationGenerators.lastInvolutionWord,pow_one] using last_square

end SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrices
