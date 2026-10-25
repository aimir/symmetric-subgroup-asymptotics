import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterWeylMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleWeylMatrix
import Mathlib.Tactic.FinCases

/-! Exact36 flat selected constant matrix products. Each coefficient proof
has literal inputs, avoiding recursive matrix normalization. The Cartan
shear in the outer Weyl matrix is retained. No original-group claim. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixData
abbrev Mat := Matrix (Fin 26) (Fin 26) (ZMod 2)

private def gate0Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {2},
    {6},
    {5},
    {4},
    {3},
    {10},
    {9},
    {8},
    {7},
    {11},
    {17},
    {15},
    {19},
    {13},
    {18},
    {12},
    {16},
    {14},
    {20},
    {24},
    {23},
    {22},
    {21},
    {25} ]
private def gate0 : Mat := fun i j => if j∈gate0Rows i then 1 else 0
private theorem gate0_entry : ∀i j : Fin 26, gate0 i j=(CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*(1 : Mat)) i j := by
  decide +kernel
private theorem gate0_eq : gate0=CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*(1 : Mat) := by
  funext i j
  exact gate0_entry i j

private def gate1Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {2},
    {6},
    {5},
    {4},
    {3},
    {10},
    {9},
    {8},
    {7},
    {11},
    {17},
    {15},
    {19},
    {13},
    {18},
    {12},
    {16},
    {14},
    {20},
    {24},
    {23},
    {22},
    {21},
    {25} ]
private def gate1 : Mat := fun i j => if j∈gate1Rows i then 1 else 0
private theorem gate1_entry : ∀i j : Fin 26, gate1 i j=((1 : Mat)*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate1_eq : gate1=(1 : Mat)*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
  funext i j
  exact gate1_entry i j

private def gate2Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {6},
    {2},
    {5},
    {10},
    {17},
    {4},
    {11},
    {15},
    {19},
    {9},
    {3},
    {8},
    {7},
    {18},
    {13},
    {24},
    {20},
    {23},
    {16},
    {12},
    {14},
    {22},
    {25},
    {21} ]
private def gate2 : Mat := fun i j => if j∈gate2Rows i then 1 else 0
private theorem gate2_entry : ∀i j : Fin 26, gate2 i j=(CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate0) i j := by
  decide +kernel
private theorem gate2_eq : gate2=CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate0 := by
  funext i j
  exact gate2_entry i j

private def gate3Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {3},
    {12},
    {7},
    {4},
    {2},
    {14},
    {13},
    {11},
    {5},
    {8},
    {21},
    {16},
    {22},
    {9},
    {20},
    {6},
    {15},
    {10},
    {18},
    {25},
    {23},
    {19},
    {17},
    {24} ]
private def gate3 : Mat := fun i j => if j∈gate3Rows i then 1 else 0
private theorem gate3_entry : ∀i j : Fin 26, gate3 i j=(gate1*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate3_eq : gate3=gate1*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix := by
  funext i j
  exact gate3_entry i j

private def gate4Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {6},
    {17},
    {10},
    {5},
    {2},
    {19},
    {15},
    {11},
    {4},
    {9},
    {24},
    {18},
    {23},
    {8},
    {20},
    {3},
    {13},
    {7},
    {16},
    {25},
    {22},
    {14},
    {12},
    {21} ]
private def gate4 : Mat := fun i j => if j∈gate4Rows i then 1 else 0
private theorem gate4_entry : ∀i j : Fin 26, gate4 i j=(CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate2) i j := by
  decide +kernel
private theorem gate4_eq : gate4=CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate2 := by
  funext i j
  exact gate4_entry i j

private def gate5Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {6},
    {17},
    {10},
    {5},
    {2},
    {19},
    {15},
    {11},
    {4},
    {9},
    {24},
    {18},
    {23},
    {8},
    {20},
    {3},
    {13},
    {7},
    {16},
    {25},
    {22},
    {14},
    {12},
    {21} ]
private def gate5 : Mat := fun i j => if j∈gate5Rows i then 1 else 0
private theorem gate5_entry : ∀i j : Fin 26, gate5 i j=(gate3*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate5_eq : gate5=gate3*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
  funext i j
  exact gate5_entry i j

private def gate6Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {17},
    {6},
    {10},
    {19},
    {24},
    {5},
    {9},
    {18},
    {23},
    {15},
    {2},
    {11},
    {4},
    {20},
    {8},
    {25},
    {16},
    {22},
    {13},
    {3},
    {7},
    {14},
    {21},
    {12} ]
private def gate6 : Mat := fun i j => if j∈gate6Rows i then 1 else 0
private theorem gate6_entry : ∀i j : Fin 26, gate6 i j=(CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate4) i j := by
  decide +kernel
private theorem gate6_eq : gate6=CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate4 := by
  funext i j
  exact gate6_entry i j

private def gate7Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {12},
    {21},
    {14},
    {7},
    {3},
    {22},
    {16},
    {8},
    {4},
    {13},
    {25},
    {20},
    {23},
    {11},
    {18},
    {2},
    {9},
    {5},
    {15},
    {24},
    {19},
    {10},
    {6},
    {17} ]
private def gate7 : Mat := fun i j => if j∈gate7Rows i then 1 else 0
private theorem gate7_entry : ∀i j : Fin 26, gate7 i j=(gate5*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate7_eq : gate7=gate5*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix := by
  funext i j
  exact gate7_entry i j

private def gate8Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {17},
    {24},
    {19},
    {10},
    {6},
    {23},
    {18},
    {9},
    {5},
    {15},
    {25},
    {20},
    {22},
    {11},
    {16},
    {2},
    {8},
    {4},
    {13},
    {21},
    {14},
    {7},
    {3},
    {12} ]
private def gate8 : Mat := fun i j => if j∈gate8Rows i then 1 else 0
private theorem gate8_entry : ∀i j : Fin 26, gate8 i j=(CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate6) i j := by
  decide +kernel
private theorem gate8_eq : gate8=CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate6 := by
  funext i j
  exact gate8_entry i j

private def gate9Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {17},
    {24},
    {19},
    {10},
    {6},
    {23},
    {18},
    {9},
    {5},
    {15},
    {25},
    {20},
    {22},
    {11},
    {16},
    {2},
    {8},
    {4},
    {13},
    {21},
    {14},
    {7},
    {3},
    {12} ]
private def gate9 : Mat := fun i j => if j∈gate9Rows i then 1 else 0
private theorem gate9_entry : ∀i j : Fin 26, gate9 i j=(gate7*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate9_eq : gate9=gate7*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
  funext i j
  exact gate9_entry i j

private def gate10Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {24},
    {17},
    {19},
    {23},
    {25},
    {10},
    {15},
    {20},
    {22},
    {18},
    {6},
    {9},
    {5},
    {16},
    {11},
    {21},
    {13},
    {14},
    {8},
    {2},
    {4},
    {7},
    {12},
    {3} ]
private def gate10 : Mat := fun i j => if j∈gate10Rows i then 1 else 0
private theorem gate10_entry : ∀i j : Fin 26, gate10 i j=(CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate8) i j := by
  decide +kernel
private theorem gate10_eq : gate10=CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate8 := by
  funext i j
  exact gate10_entry i j

private def gate11Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {21},
    {25},
    {22},
    {14},
    {12},
    {23},
    {20},
    {13},
    {7},
    {16},
    {24},
    {18},
    {19},
    {8},
    {15},
    {3},
    {11},
    {4},
    {9},
    {17},
    {10},
    {5},
    {2},
    {6} ]
private def gate11 : Mat := fun i j => if j∈gate11Rows i then 1 else 0
private theorem gate11_entry : ∀i j : Fin 26, gate11 i j=(gate9*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate11_eq : gate11=gate9*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix := by
  funext i j
  exact gate11_entry i j

private def gate12Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {24},
    {25},
    {23},
    {19},
    {17},
    {22},
    {20},
    {15},
    {10},
    {18},
    {21},
    {16},
    {14},
    {9},
    {13},
    {6},
    {11},
    {5},
    {8},
    {12},
    {7},
    {4},
    {2},
    {3} ]
private def gate12 : Mat := fun i j => if j∈gate12Rows i then 1 else 0
private theorem gate12_entry : ∀i j : Fin 26, gate12 i j=(CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate10) i j := by
  decide +kernel
private theorem gate12_eq : gate12=CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*gate10 := by
  funext i j
  exact gate12_entry i j

private def gate13Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {24},
    {25},
    {23},
    {19},
    {17},
    {22},
    {20},
    {15},
    {10},
    {18},
    {21},
    {16},
    {14},
    {9},
    {13},
    {6},
    {11},
    {5},
    {8},
    {12},
    {7},
    {4},
    {2},
    {3} ]
private def gate13 : Mat := fun i j => if j∈gate13Rows i then 1 else 0
private theorem gate13_entry : ∀i j : Fin 26, gate13 i j=(gate11*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate13_eq : gate13=gate11*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
  funext i j
  exact gate13_entry i j

private def gate14Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {25},
    {24},
    {23},
    {22},
    {21},
    {19},
    {18},
    {16},
    {14},
    {20},
    {17},
    {15},
    {10},
    {13},
    {9},
    {12},
    {8},
    {7},
    {11},
    {6},
    {5},
    {4},
    {3},
    {2} ]
private def gate14 : Mat := fun i j => if j∈gate14Rows i then 1 else 0
private theorem gate14_entry : ∀i j : Fin 26, gate14 i j=(CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate12) i j := by
  decide +kernel
private theorem gate14_eq : gate14=CFSGReeFFourBinarySeedOuterWeylMatrix.matrix*gate12 := by
  funext i j
  exact gate14_entry i j

private def gate15Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {25},
    {24},
    {23},
    {22},
    {21},
    {19},
    {18},
    {16},
    {14},
    {20},
    {17},
    {15},
    {10},
    {13},
    {9},
    {12},
    {8},
    {7},
    {11},
    {6},
    {5},
    {4},
    {3},
    {2} ]
private def gate15 : Mat := fun i j => if j∈gate15Rows i then 1 else 0
private theorem gate15_entry : ∀i j : Fin 26, gate15 i j=(gate13*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix) i j := by
  decide +kernel
private theorem gate15_eq : gate15=gate13*CFSGReeFFourBinarySeedOuterWeylMatrix.matrix := by
  funext i j
  exact gate15_entry i j

private def gate16Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,12,13},
    {2},
    {3},
    {3,4},
    {4,5},
    {3,4,5,6},
    {7},
    {7,8},
    {8,9},
    {7,8,9,10},
    {11},
    {12},
    {12,13},
    {14},
    {0,13,15},
    {14,16},
    {12,13,15,17},
    {16,18},
    {14,16,18,19},
    {20},
    {21},
    {21,22},
    {22,23},
    {21,22,23,24},
    {25} ]
private def gate16 : Mat := fun i j => if j∈gate16Rows i then 1 else 0
private theorem gate16_entry : ∀i j : Fin 26, gate16 i j=((1 : Mat)*CFSGReeFFourBinarySeedMiddleMatrix.matrix) i j := by
  decide +kernel
private theorem gate16_eq : gate16=(1 : Mat)*CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  funext i j
  exact gate16_entry i j

private def gate17Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,12,13},
    {2},
    {3},
    {3,4},
    {4,5},
    {3,4,5,6},
    {7},
    {7,8},
    {8,9},
    {7,8,9,10},
    {11},
    {12},
    {12,13},
    {14},
    {0,13,15},
    {14,16},
    {12,13,15,17},
    {16,18},
    {14,16,18,19},
    {20},
    {21},
    {21,22},
    {22,23},
    {21,22,23,24},
    {25} ]
private def gate17 : Mat := fun i j => if j∈gate17Rows i then 1 else 0
private theorem gate17_entry : ∀i j : Fin 26, gate17 i j=(gate16*(1 : Mat)) i j := by
  decide +kernel
private theorem gate17_eq : gate17=gate16*(1 : Mat) := by
  funext i j
  exact gate17_entry i j

private def gate18Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,10},
    {1},
    {2},
    {6},
    {5},
    {4},
    {2,3},
    {10},
    {9},
    {6,8},
    {5,7},
    {6,11},
    {17},
    {15},
    {19},
    {9,13},
    {17,18},
    {6,8,11,12},
    {15,16},
    {1,10,14},
    {17,20},
    {24},
    {23},
    {19,22},
    {17,18,20,21},
    {24,25} ]
private def gate18 : Mat := fun i j => if j∈gate18Rows i then 1 else 0
private theorem gate18_entry : ∀i j : Fin 26, gate18 i j=(gate1*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix) i j := by
  decide +kernel
private theorem gate18_eq : gate18=gate1*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix := by
  funext i j
  exact gate18_entry i j

private def gate19Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,7},
    {1},
    {2},
    {3},
    {4},
    {5},
    {2,6},
    {7},
    {8},
    {3,9},
    {4,10},
    {3,11},
    {12},
    {13},
    {14},
    {8,15},
    {12,16},
    {3,9,11,17},
    {13,18},
    {1,7,19},
    {12,20},
    {21},
    {22},
    {14,23},
    {12,16,20,24},
    {21,25} ]
private def gate19 : Mat := fun i j => if j∈gate19Rows i then 1 else 0
private theorem gate19_entry : ∀i j : Fin 26, gate19 i j=(gate18*gate0) i j := by
  decide +kernel
private theorem gate19_eq : gate19=gate18*gate0 := by
  funext i j
  exact gate19_entry i j

private def gate20Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1,12,13},
    {1,12,13},
    {3},
    {12},
    {7},
    {3,4},
    {2},
    {14},
    {12,13},
    {11},
    {4,5},
    {7,8},
    {21},
    {14,16},
    {21,22},
    {8,9},
    {20},
    {3,4,5,6},
    {0,13,15},
    {7,8,9,10},
    {16,18},
    {25},
    {22,23},
    {14,16,18,19},
    {12,13,15,17},
    {21,22,23,24} ]
private def gate20 : Mat := fun i j => if j∈gate20Rows i then 1 else 0
private theorem gate20_entry : ∀i j : Fin 26, gate20 i j=(gate3*CFSGReeFFourBinarySeedMiddleMatrix.matrix) i j := by
  decide +kernel
private theorem gate20_eq : gate20=gate3*CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  funext i j
  exact gate20_entry i j

private def gate21Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,3,8},
    {1,3,8},
    {2},
    {3},
    {4},
    {2,5},
    {6},
    {7},
    {3,8},
    {9},
    {5,10},
    {4,11},
    {12},
    {7,13},
    {12,14},
    {11,15},
    {16},
    {2,5,10,17},
    {0,1,8,18},
    {4,11,15,19},
    {13,20},
    {21},
    {14,22},
    {7,13,20,23},
    {3,8,18,24},
    {12,14,22,25} ]
private def gate21 : Mat := fun i j => if j∈gate21Rows i then 1 else 0
private theorem gate21_entry : ∀i j : Fin 26, gate21 i j=(gate20*gate2) i j := by
  decide +kernel
private theorem gate21_eq : gate21=gate20*gate2 := by
  funext i j
  exact gate21_entry i j

private def gate22Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1,10},
    {1},
    {6},
    {17},
    {10},
    {5},
    {2},
    {19},
    {15},
    {6,11},
    {4},
    {9},
    {24},
    {17,18},
    {23},
    {6,8},
    {17,20},
    {2,3},
    {9,13},
    {5,7},
    {15,16},
    {24,25},
    {19,22},
    {1,10,14},
    {6,8,11,12},
    {17,18,20,21} ]
private def gate22 : Mat := fun i j => if j∈gate22Rows i then 1 else 0
private theorem gate22_entry : ∀i j : Fin 26, gate22 i j=(gate5*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix) i j := by
  decide +kernel
private theorem gate22_eq : gate22=gate5*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix := by
  funext i j
  exact gate22_entry i j

private def gate23Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,4},
    {1},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {2,9},
    {10},
    {11},
    {12},
    {3,13},
    {14},
    {2,15},
    {3,16},
    {6,17},
    {11,18},
    {5,19},
    {8,20},
    {12,21},
    {7,22},
    {1,4,23},
    {2,9,15,24},
    {3,13,16,25} ]
private def gate23 : Mat := fun i j => if j∈gate23Rows i then 1 else 0
private theorem gate23_entry : ∀i j : Fin 26, gate23 i j=(gate22*gate4) i j := by
  decide +kernel
private theorem gate23_eq : gate23=gate22*gate4 := by
  funext i j
  exact gate23_entry i j

private def gate24Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,12,13},
    {12},
    {21},
    {14},
    {7},
    {3},
    {21,22},
    {14,16},
    {7,8},
    {3,4},
    {12,13},
    {25},
    {20},
    {22,23},
    {11},
    {16,18},
    {2},
    {8,9},
    {4,5},
    {0,13,15},
    {21,22,23,24},
    {14,16,18,19},
    {7,8,9,10},
    {3,4,5,6},
    {12,13,15,17} ]
private def gate24 : Mat := fun i j => if j∈gate24Rows i then 1 else 0
private theorem gate24_entry : ∀i j : Fin 26, gate24 i j=(gate7*CFSGReeFFourBinarySeedMiddleMatrix.matrix) i j := by
  decide +kernel
private theorem gate24_eq : gate24=gate7*CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  funext i j
  exact gate24_entry i j

private def gate25Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,2,11},
    {2},
    {3},
    {4},
    {5},
    {6},
    {3,7},
    {4,8},
    {5,9},
    {6,10},
    {2,11},
    {12},
    {13},
    {7,14},
    {15},
    {8,16},
    {17},
    {9,18},
    {10,19},
    {0,11,20},
    {3,7,14,21},
    {4,8,16,22},
    {5,9,18,23},
    {6,10,19,24},
    {2,11,20,25} ]
private def gate25 : Mat := fun i j => if j∈gate25Rows i then 1 else 0
private theorem gate25_entry : ∀i j : Fin 26, gate25 i j=(gate24*gate6) i j := by
  decide +kernel
private theorem gate25_eq : gate25=gate24*gate6 := by
  funext i j
  exact gate25_entry i j

private def gate26Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,10},
    {1},
    {17},
    {24},
    {19},
    {10},
    {6},
    {23},
    {17,18},
    {9},
    {5},
    {15},
    {24,25},
    {17,20},
    {19,22},
    {6,11},
    {15,16},
    {2},
    {6,8},
    {4},
    {9,13},
    {17,18,20,21},
    {1,10,14},
    {5,7},
    {2,3},
    {6,8,11,12} ]
private def gate26 : Mat := fun i j => if j∈gate26Rows i then 1 else 0
private theorem gate26_entry : ∀i j : Fin 26, gate26 i j=(gate9*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix) i j := by
  decide +kernel
private theorem gate26_eq : gate26=gate9*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix := by
  funext i j
  exact gate26_entry i j

private def gate27Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,5},
    {1},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {2,8},
    {9},
    {10},
    {11},
    {3,12},
    {2,13},
    {4,14},
    {6,15},
    {11,16},
    {17},
    {6,18},
    {19},
    {9,20},
    {2,8,13,21},
    {1,5,22},
    {10,23},
    {17,24},
    {6,15,18,25} ]
private def gate27 : Mat := fun i j => if j∈gate27Rows i then 1 else 0
private theorem gate27_entry : ∀i j : Fin 26, gate27 i j=(gate26*gate8) i j := by
  decide +kernel
private theorem gate27_eq : gate27=gate26*gate8 := by
  funext i j
  exact gate27_entry i j

private def gate28Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1,12,13},
    {1,12,13},
    {21},
    {25},
    {21,22},
    {14},
    {12},
    {22,23},
    {20},
    {12,13},
    {7},
    {14,16},
    {21,22,23,24},
    {16,18},
    {14,16,18,19},
    {7,8},
    {0,13,15},
    {3},
    {11},
    {3,4},
    {8,9},
    {12,13,15,17},
    {7,8,9,10},
    {4,5},
    {2},
    {3,4,5,6} ]
private def gate28 : Mat := fun i j => if j∈gate28Rows i then 1 else 0
private theorem gate28_entry : ∀i j : Fin 26, gate28 i j=(gate11*CFSGReeFFourBinarySeedMiddleMatrix.matrix) i j := by
  decide +kernel
private theorem gate28_eq : gate28=gate11*CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  funext i j
  exact gate28_entry i j

private def gate29Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,6,9},
    {1,6,9},
    {2},
    {3},
    {2,4},
    {5},
    {6},
    {4,7},
    {8},
    {6,9},
    {10},
    {5,11},
    {2,4,7,12},
    {11,13},
    {5,11,13,14},
    {10,15},
    {0,1,9,16},
    {17},
    {18},
    {17,19},
    {15,20},
    {6,9,16,21},
    {10,15,20,22},
    {19,23},
    {24},
    {17,19,23,25} ]
private def gate29 : Mat := fun i j => if j∈gate29Rows i then 1 else 0
private theorem gate29_entry : ∀i j : Fin 26, gate29 i j=(gate28*gate10) i j := by
  decide +kernel
private theorem gate29_eq : gate29=gate28*gate10 := by
  funext i j
  exact gate29_entry i j

private def gate30Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1,10},
    {1},
    {24},
    {24,25},
    {23},
    {19},
    {17},
    {19,22},
    {17,20},
    {15},
    {10},
    {17,18},
    {17,18,20,21},
    {15,16},
    {1,10,14},
    {9},
    {9,13},
    {6},
    {6,11},
    {5},
    {6,8},
    {6,8,11,12},
    {5,7},
    {4},
    {2},
    {2,3} ]
private def gate30 : Mat := fun i j => if j∈gate30Rows i then 1 else 0
private theorem gate30_entry : ∀i j : Fin 26, gate30 i j=(gate13*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix) i j := by
  decide +kernel
private theorem gate30_eq : gate30=gate13*CFSGReeFFourBinarySeedOuterMatrix.outerMatrix := by
  funext i j
  exact gate30_entry i j

private def gate31Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,10},
    {1},
    {2},
    {2,3},
    {4},
    {5},
    {6},
    {5,7},
    {6,8},
    {9},
    {10},
    {6,11},
    {6,8,11,12},
    {9,13},
    {1,10,14},
    {15},
    {15,16},
    {17},
    {17,18},
    {19},
    {17,20},
    {17,18,20,21},
    {19,22},
    {23},
    {24},
    {24,25} ]
private def gate31 : Mat := fun i j => if j∈gate31Rows i then 1 else 0
private theorem gate31_entry : ∀i j : Fin 26, gate31 i j=(gate30*gate12) i j := by
  decide +kernel
private theorem gate31_eq : gate31=gate30*gate12 := by
  funext i j
  exact gate31_entry i j

private def gate32Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,12},
    {2},
    {3},
    {4},
    {3,5},
    {3,4,6},
    {7},
    {8},
    {7,9},
    {7,8,10},
    {11},
    {12},
    {13},
    {14},
    {12,15},
    {16},
    {0,12,13,17},
    {14,18},
    {14,16,19},
    {20},
    {21},
    {22},
    {21,23},
    {21,22,24},
    {25} ]
private def gate32 : Mat := fun i j => if j∈gate32Rows i then 1 else 0
private theorem gate32_entry : ∀i j : Fin 26, gate32 i j=(gate17*gate17) i j := by
  decide +kernel
private theorem gate32_eq : gate32=gate17*gate17 := by
  funext i j
  exact gate32_entry i j

private def gate33Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,3},
    {1,3},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {9},
    {2,10},
    {11},
    {12},
    {13},
    {14},
    {4,15},
    {16},
    {2,5,17},
    {3,18},
    {4,11,19},
    {7,20},
    {21},
    {12,22},
    {7,13,23},
    {0,1,3,8,24},
    {12,14,25} ]
private def gate33 : Mat := fun i j => if j∈gate33Rows i then 1 else 0
private theorem gate33_entry : ∀i j : Fin 26, gate33 i j=(gate21*gate21) i j := by
  decide +kernel
private theorem gate33_eq : gate33=gate21*gate21 := by
  funext i j
  exact gate33_entry i j

private def gate34Rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,2},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {9},
    {10},
    {11},
    {12},
    {13},
    {3,14},
    {15},
    {4,16},
    {17},
    {5,18},
    {6,19},
    {2,20},
    {3,7,21},
    {4,8,22},
    {5,9,23},
    {6,10,24},
    {0,2,11,25} ]
private def gate34 : Mat := fun i j => if j∈gate34Rows i then 1 else 0
private theorem gate34_entry : ∀i j : Fin 26, gate34 i j=(gate25*gate25) i j := by
  decide +kernel
private theorem gate34_eq : gate34=gate25*gate25 := by
  funext i j
  exact gate34_entry i j

private def gate35Rows : Fin 26 → Finset (Fin 26) :=
  ![{0,6},
    {1,6},
    {2},
    {3},
    {4},
    {5},
    {6},
    {2,7},
    {8},
    {9},
    {10},
    {11},
    {2,4,12},
    {5,13},
    {5,11,14},
    {15},
    {6,16},
    {17},
    {18},
    {19},
    {10,20},
    {0,1,6,9,21},
    {10,15,22},
    {17,23},
    {24},
    {17,19,25} ]
private def gate35 : Mat := fun i j => if j∈gate35Rows i then 1 else 0
private theorem gate35_entry : ∀i j : Fin 26, gate35 i j=(gate29*gate29) i j := by
  decide +kernel
private theorem gate35_eq : gate35=gate29*gate29 := by
  funext i j
  exact gate35_entry i j

def stepMatrix (n : ℕ) : Mat :=
  if n%2=0 then CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix else CFSGReeFFourBinarySeedOuterWeylMatrix.matrix

def prefixMatrix : Fin 9 → Mat :=
  ![(1 : Mat),gate0,gate2,gate4,gate6,gate8,gate10,gate12,gate14]

def backMatrix : Fin 9 → Mat :=
  ![(1 : Mat),gate1,gate3,gate5,gate7,gate9,gate11,gate13,gate15]

def axisMatrix : Fin 8 → Mat :=
  ![gate17,gate19,gate21,gate23,gate25,gate27,gate29,gate31]

def bitMatrix : Fin 12 → Mat :=
  ![gate17,gate32,gate19,gate21,gate33,gate23,gate25,gate34,gate27,gate29,gate35,gate31]

theorem prefix_zero : prefixMatrix 0=1 := rfl
theorem back_zero : backMatrix 0=1 := rfl

theorem prefix_step (i : Fin 8) : prefixMatrix i.succ=stepMatrix i.val*prefixMatrix i.castSucc := by
  fin_cases i
  · exact gate0_eq
  · exact gate2_eq
  · exact gate4_eq
  · exact gate6_eq
  · exact gate8_eq
  · exact gate10_eq
  · exact gate12_eq
  · exact gate14_eq

theorem back_step (i : Fin 8) : backMatrix i.succ=backMatrix i.castSucc*stepMatrix i.val := by
  fin_cases i
  · exact gate1_eq
  · exact gate3_eq
  · exact gate5_eq
  · exact gate7_eq
  · exact gate9_eq
  · exact gate11_eq
  · exact gate13_eq
  · exact gate15_eq

theorem axis_eq (i : Fin 8) : axisMatrix i=backMatrix i.castSucc*
    (if i.val%2=0 then CFSGReeFFourBinarySeedMiddleMatrix.matrix else CFSGReeFFourBinarySeedOuterMatrix.outerMatrix)*prefixMatrix i.castSucc := by
  fin_cases i
  · exact gate17_eq.trans (congrArg (fun T : Mat => T*(1 : Mat)) gate16_eq)
  · exact gate19_eq.trans (congrArg (fun T : Mat => T*gate0) gate18_eq)
  · exact gate21_eq.trans (congrArg (fun T : Mat => T*gate2) gate20_eq)
  · exact gate23_eq.trans (congrArg (fun T : Mat => T*gate4) gate22_eq)
  · exact gate25_eq.trans (congrArg (fun T : Mat => T*gate6) gate24_eq)
  · exact gate27_eq.trans (congrArg (fun T : Mat => T*gate8) gate26_eq)
  · exact gate29_eq.trans (congrArg (fun T : Mat => T*gate10) gate28_eq)
  · exact gate31_eq.trans (congrArg (fun T : Mat => T*gate12) gate30_eq)

private theorem twelve_projections_ext {T : Type} (f g : Fin 12 → T)
    (h0 : f 0=g 0) (h1 : f 1=g 1) (h2 : f 2=g 2) (h3 : f 3=g 3)
    (h4 : f 4=g 4) (h5 : f 5=g 5) (h6 : f 6=g 6) (h7 : f 7=g 7)
    (h8 : f 8=g 8) (h9 : f 9=g 9) (h10 : f 10=g 10) (h11 : f 11=g 11) :
    f=g := by
  funext i
  fin_cases i <;> assumption

def bitSource : Fin 12 → Fin 8 := ![0,0,1,2,2,3,4,4,5,6,6,7]
def bitSquared : Fin 12 → Bool :=
  ![false,true,false,false,true,false,false,true,false,false,true,false]

def bitAxisDescription (i : Fin 12) : Mat :=
  let A : Mat := axisMatrix (bitSource i)
  if bitSquared i then A*A else A

private theorem bit_projection0 : bitMatrix 0=bitAxisDescription 0 := by
  rfl

private theorem bit_projection1 : bitMatrix 1=bitAxisDescription 1 := by
  change gate32=gate17*gate17
  exact gate32_eq

private theorem bit_projection2 : bitMatrix 2=bitAxisDescription 2 := by
  rfl

private theorem bit_projection3 : bitMatrix 3=bitAxisDescription 3 := by
  rfl

private theorem bit_projection4 : bitMatrix 4=bitAxisDescription 4 := by
  change gate33=gate21*gate21
  exact gate33_eq

private theorem bit_projection5 : bitMatrix 5=bitAxisDescription 5 := by
  rfl

private theorem bit_projection6 : bitMatrix 6=bitAxisDescription 6 := by
  rfl

private theorem bit_projection7 : bitMatrix 7=bitAxisDescription 7 := by
  change gate34=gate25*gate25
  exact gate34_eq

private theorem bit_projection8 : bitMatrix 8=bitAxisDescription 8 := by
  rfl

private theorem bit_projection9 : bitMatrix 9=bitAxisDescription 9 := by
  rfl

private theorem bit_projection10 : bitMatrix 10=bitAxisDescription 10 := by
  change gate35=gate29*gate29
  exact gate35_eq

private theorem bit_projection11 : bitMatrix 11=bitAxisDescription 11 := by
  rfl

theorem bitMatrix_eq : bitMatrix=bitAxisDescription :=
  twelve_projections_ext bitMatrix bitAxisDescription
    bit_projection0 bit_projection1 bit_projection2 bit_projection3 bit_projection4 bit_projection5 bit_projection6 bit_projection7 bit_projection8 bit_projection9 bit_projection10 bit_projection11

def bitRows0 : Fin 26 → Finset (Fin 26) := ![{0},
    {1,12,13},
    {2},
    {3},
    {3,4},
    {4,5},
    {3,4,5,6},
    {7},
    {7,8},
    {8,9},
    {7,8,9,10},
    {11},
    {12},
    {12,13},
    {14},
    {0,13,15},
    {14,16},
    {12,13,15,17},
    {16,18},
    {14,16,18,19},
    {20},
    {21},
    {21,22},
    {22,23},
    {21,22,23,24},
    {25} ]
theorem bit_entry0 (r c : Fin 26) : bitMatrix 0 r c=(if c∈bitRows0 r then 1 else 0) := rfl

def bitRows1 : Fin 26 → Finset (Fin 26) := ![{0},
    {1,12},
    {2},
    {3},
    {4},
    {3,5},
    {3,4,6},
    {7},
    {8},
    {7,9},
    {7,8,10},
    {11},
    {12},
    {13},
    {14},
    {12,15},
    {16},
    {0,12,13,17},
    {14,18},
    {14,16,19},
    {20},
    {21},
    {22},
    {21,23},
    {21,22,24},
    {25} ]
theorem bit_entry1 (r c : Fin 26) : bitMatrix 1 r c=(if c∈bitRows1 r then 1 else 0) := rfl

def bitRows2 : Fin 26 → Finset (Fin 26) := ![{0,7},
    {1},
    {2},
    {3},
    {4},
    {5},
    {2,6},
    {7},
    {8},
    {3,9},
    {4,10},
    {3,11},
    {12},
    {13},
    {14},
    {8,15},
    {12,16},
    {3,9,11,17},
    {13,18},
    {1,7,19},
    {12,20},
    {21},
    {22},
    {14,23},
    {12,16,20,24},
    {21,25} ]
theorem bit_entry2 (r c : Fin 26) : bitMatrix 2 r c=(if c∈bitRows2 r then 1 else 0) := rfl

def bitRows3 : Fin 26 → Finset (Fin 26) := ![{0,3,8},
    {1,3,8},
    {2},
    {3},
    {4},
    {2,5},
    {6},
    {7},
    {3,8},
    {9},
    {5,10},
    {4,11},
    {12},
    {7,13},
    {12,14},
    {11,15},
    {16},
    {2,5,10,17},
    {0,1,8,18},
    {4,11,15,19},
    {13,20},
    {21},
    {14,22},
    {7,13,20,23},
    {3,8,18,24},
    {12,14,22,25} ]
theorem bit_entry3 (r c : Fin 26) : bitMatrix 3 r c=(if c∈bitRows3 r then 1 else 0) := rfl

def bitRows4 : Fin 26 → Finset (Fin 26) := ![{0,3},
    {1,3},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {9},
    {2,10},
    {11},
    {12},
    {13},
    {14},
    {4,15},
    {16},
    {2,5,17},
    {3,18},
    {4,11,19},
    {7,20},
    {21},
    {12,22},
    {7,13,23},
    {0,1,3,8,24},
    {12,14,25} ]
theorem bit_entry4 (r c : Fin 26) : bitMatrix 4 r c=(if c∈bitRows4 r then 1 else 0) := rfl

def bitRows5 : Fin 26 → Finset (Fin 26) := ![{0,4},
    {1},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {2,9},
    {10},
    {11},
    {12},
    {3,13},
    {14},
    {2,15},
    {3,16},
    {6,17},
    {11,18},
    {5,19},
    {8,20},
    {12,21},
    {7,22},
    {1,4,23},
    {2,9,15,24},
    {3,13,16,25} ]
theorem bit_entry5 (r c : Fin 26) : bitMatrix 5 r c=(if c∈bitRows5 r then 1 else 0) := rfl

def bitRows6 : Fin 26 → Finset (Fin 26) := ![{0},
    {1,2,11},
    {2},
    {3},
    {4},
    {5},
    {6},
    {3,7},
    {4,8},
    {5,9},
    {6,10},
    {2,11},
    {12},
    {13},
    {7,14},
    {15},
    {8,16},
    {17},
    {9,18},
    {10,19},
    {0,11,20},
    {3,7,14,21},
    {4,8,16,22},
    {5,9,18,23},
    {6,10,19,24},
    {2,11,20,25} ]
theorem bit_entry6 (r c : Fin 26) : bitMatrix 6 r c=(if c∈bitRows6 r then 1 else 0) := rfl

def bitRows7 : Fin 26 → Finset (Fin 26) := ![{0},
    {1,2},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {9},
    {10},
    {11},
    {12},
    {13},
    {3,14},
    {15},
    {4,16},
    {17},
    {5,18},
    {6,19},
    {2,20},
    {3,7,21},
    {4,8,22},
    {5,9,23},
    {6,10,24},
    {0,2,11,25} ]
theorem bit_entry7 (r c : Fin 26) : bitMatrix 7 r c=(if c∈bitRows7 r then 1 else 0) := rfl

def bitRows8 : Fin 26 → Finset (Fin 26) := ![{0,5},
    {1},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {2,8},
    {9},
    {10},
    {11},
    {3,12},
    {2,13},
    {4,14},
    {6,15},
    {11,16},
    {17},
    {6,18},
    {19},
    {9,20},
    {2,8,13,21},
    {1,5,22},
    {10,23},
    {17,24},
    {6,15,18,25} ]
theorem bit_entry8 (r c : Fin 26) : bitMatrix 8 r c=(if c∈bitRows8 r then 1 else 0) := rfl

def bitRows9 : Fin 26 → Finset (Fin 26) := ![{0,6,9},
    {1,6,9},
    {2},
    {3},
    {2,4},
    {5},
    {6},
    {4,7},
    {8},
    {6,9},
    {10},
    {5,11},
    {2,4,7,12},
    {11,13},
    {5,11,13,14},
    {10,15},
    {0,1,9,16},
    {17},
    {18},
    {17,19},
    {15,20},
    {6,9,16,21},
    {10,15,20,22},
    {19,23},
    {24},
    {17,19,23,25} ]
theorem bit_entry9 (r c : Fin 26) : bitMatrix 9 r c=(if c∈bitRows9 r then 1 else 0) := rfl

def bitRows10 : Fin 26 → Finset (Fin 26) := ![{0,6},
    {1,6},
    {2},
    {3},
    {4},
    {5},
    {6},
    {2,7},
    {8},
    {9},
    {10},
    {11},
    {2,4,12},
    {5,13},
    {5,11,14},
    {15},
    {6,16},
    {17},
    {18},
    {19},
    {10,20},
    {0,1,6,9,21},
    {10,15,22},
    {17,23},
    {24},
    {17,19,25} ]
theorem bit_entry10 (r c : Fin 26) : bitMatrix 10 r c=(if c∈bitRows10 r then 1 else 0) := rfl

def bitRows11 : Fin 26 → Finset (Fin 26) := ![{0,10},
    {1},
    {2},
    {2,3},
    {4},
    {5},
    {6},
    {5,7},
    {6,8},
    {9},
    {10},
    {6,11},
    {6,8,11,12},
    {9,13},
    {1,10,14},
    {15},
    {15,16},
    {17},
    {17,18},
    {19},
    {17,20},
    {17,18,20,21},
    {19,22},
    {23},
    {24},
    {24,25} ]
theorem bit_entry11 (r c : Fin 26) : bitMatrix 11 r c=(if c∈bitRows11 r then 1 else 0) := rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixData
