import SymmetricSubgroupAsymptotics.BinaryLinearConstraintCertificate
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-! Square carries for the two extremal invariant kernels of the literal
regular-eight action. All three lift offsets remain arbitrary. Only the
actual square-in-kernel and commutator-in-radical constraints are used.
The sparse row witnesses are checked on 24 coordinate basis vectors,
without enumerating any of the 2^24 assignments. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry

abbrev V := Fin 8 → ZMod 2
abbrev Offsets := Fin 24 → ZMod 2

/-- The original three 8T3 generator permutations, in original label order. -/
def generatorImages : Fin 3 → Fin 8 → Fin 8 :=
  ![![7, 2, 1, 4, 3, 6, 5, 0],
    ![2, 7, 0, 5, 6, 3, 4, 1],
    ![4, 5, 6, 7, 0, 1, 2, 3]]

theorem generatorImages_eq_original : ∀ i j,
    generatorImages i j = BinaryMenuCayley8T3.generators i j := by decide +kernel

theorem generator_involution : ∀ i j,
    generatorImages i (generatorImages i j) = j := by decide +kernel

theorem generators_commute : ∀ i j k,
    generatorImages i (generatorImages j k) =
      generatorImages j (generatorImages i k) := by decide +kernel

def offsetProjection (i : Fin 3) : Offsets →ₗ[ZMod 2] V where
  toFun x j := x (finProdFinEquiv (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def difference (i : Fin 3) : V →ₗ[ZMod 2] V where
  toFun v j := v (generatorImages i j) - v j
  map_add' := by intro v w; ext j; simp only [Pi.add_apply]; ring
  map_smul' := by intro c v; ext j; simp only [Pi.smul_apply, smul_sub, RingHom.id_apply]

/-- The actual square displacement D_i(v_i) of the ith involutory lift. -/
def squareDisplacement (i : Fin 3) : Offsets →ₗ[ZMod 2] V :=
  (difference i).comp (offsetProjection i)

/-- The actual discrepancy between the products of the two lifts. -/
def commutatorDisplacement (i j : Fin 3) : Offsets →ₗ[ZMod 2] V :=
  (difference j).comp (offsetProjection i) +
    (difference i).comp (offsetProjection j)

def pairs : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

def squareFunctional (i : Fin 3) (chi : V) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  (binaryRowFunctional chi).comp (squareDisplacement i)

def commutatorFunctional (p : Fin 3) (chi : V) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  (binaryRowFunctional chi).comp
    (commutatorDisplacement (pairs p).1 (pairs p).2)

def annihilatorSpace {a : ℕ} (masks : Fin a → ℕ) : Submodule (ZMod 2) V :=
  ⨅ i, (binaryRowFunctional (binaryVectorOfMask 8 (masks i))).ker

def annihilatorK45 : Fin 1 → ℕ := ![255]
def annihilatorR45 : Fin 4 → ℕ := ![135, 75, 45, 30]
def annihilatorK46 : Fin 4 → ℕ := ![135, 75, 45, 30]
def annihilatorR46 : Fin 7 → ℕ := ![129, 65, 33, 17, 9, 5, 3]

abbrev K45 := annihilatorSpace annihilatorK45
abbrev R45 := annihilatorSpace annihilatorR45
abbrev K46 := annihilatorSpace annihilatorK46
abbrev R46 := annihilatorSpace annihilatorR46

private def input45Mask : Fin 15 → ℕ :=
  ![0, 0, 0, 0, 65535, 65280, 255, 255, 16711935, 16711935, 255,
    65280, 16776960, 65280, 16776960]
private def target45Mask : Fin 12 → ℕ :=
  ![0, 255, 255, 0, 0, 65280, 0, 65280, 16711680, 16711680, 16711680, 16711680]
private def combination45Mask : Fin 12 → ℕ :=
  ![0, 48, 48, 0, 0, 32, 0, 32, 304, 304, 304, 304]
private def input45 (i : Fin 15) := binaryVectorOfMask 24 (input45Mask i)
private def target45 (j : Fin 12) := binaryVectorOfMask 24 (target45Mask j)

private def input45Actual (k : Fin 15) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : k.val < 3 then
    squareFunctional ⟨k.val, h⟩ (binaryVectorOfMask 8 255)
  else
    commutatorFunctional ⟨(k.val - 3) / 4, by omega⟩
      (binaryVectorOfMask 8 (annihilatorR45 ⟨(k.val - 3) % 4, by omega⟩))

private def target45Actual (k : Fin 12) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  squareFunctional ⟨k.val / 4, by omega⟩
    (binaryVectorOfMask 8 (annihilatorR45 ⟨k.val % 4, by omega⟩))

private theorem input45_basis : ∀ i j,
    binaryRowFunctional (input45 i) (Pi.single j 1) =
      input45Actual i (Pi.single j 1) := by decide +kernel

private theorem target45_basis : ∀ i j,
    binaryRowFunctional (target45 i) (Pi.single j 1) =
      target45Actual i (Pi.single j 1) := by decide +kernel

private def certificate45 : BinaryLinearConstraintCertificate input45 target45 where
  support j := Finset.univ.filter fun i => (combination45Mask j).testBit i.val
  target_eq := by decide +kernel

private def input46Mask : Fin 33 → ℕ :=
  ![0, 255, 255, 0, 0, 65280, 0, 65280, 16711680, 16711680, 16711680,
    16711680, 135, 57685, 57645, 39253, 39213, 34560, 34695, 153,
    14745685, 14745651, 10027008, 10027161, 8847445, 8847411,
    8886528, 5592320, 2962176, 5570560, 2988288, 21760, 8860416]
private def target46Mask : Fin 21 → ℕ :=
  ![0, 225, 225, 153, 153, 135, 135, 34560, 21760, 11520, 21760,
    11520, 0, 34560, 10027008, 5570560, 3342336, 0, 10027008, 5570560, 3342336]
private def combination46Mask : Fin 21 → ℕ :=
  ![0, 528386, 528386, 524288, 524288, 4096, 4096, 40992, 671088640,
    671129600, 671088640, 671129600, 0, 40992, 4194304, 536870912,
    541065472, 0, 4194304, 536870912, 541065472]
private def input46 (i : Fin 33) := binaryVectorOfMask 24 (input46Mask i)
private def target46 (j : Fin 21) := binaryVectorOfMask 24 (target46Mask j)

private def input46Actual (k : Fin 33) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : k.val < 12 then
    squareFunctional ⟨k.val / 4, by omega⟩
      (binaryVectorOfMask 8 (annihilatorK46 ⟨k.val % 4, by omega⟩))
  else
    commutatorFunctional ⟨(k.val - 12) / 7, by omega⟩
      (binaryVectorOfMask 8 (annihilatorR46 ⟨(k.val - 12) % 7, by omega⟩))

private def target46Actual (k : Fin 21) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  squareFunctional ⟨k.val / 7, by omega⟩
    (binaryVectorOfMask 8 (annihilatorR46 ⟨k.val % 7, by omega⟩))

private theorem input46_basis : ∀ i j,
    binaryRowFunctional (input46 i) (Pi.single j 1) =
      input46Actual i (Pi.single j 1) := by decide +kernel

private theorem target46_basis : ∀ i j,
    binaryRowFunctional (target46 i) (Pi.single j 1) =
      target46Actual i (Pi.single j 1) := by decide +kernel

private def certificate46 : BinaryLinearConstraintCertificate input46 target46 where
  support j := Finset.univ.filter fun i => (combination46Mask j).testBit i.val
  target_eq := by decide +kernel

/-- For the augmentation kernel J, square-in-J and commuting modulo J²
force all three square carries into J². -/
theorem square_carry45 (x : Offsets)
    (hsquare : ∀ i, squareDisplacement i x ∈ K45)
    (hcomm : ∀ p,
      commutatorDisplacement (pairs p).1 (pairs p).2 x ∈ R45) :
    ∀ i, squareDisplacement i x ∈ R45 := by
  have hinput (k : Fin 15) : dotProduct (input45 k) x = 0 := by
    change binaryRowFunctional (input45 k) x = 0
    rw [binaryLinearFunctional_ext_basis (input45_basis k)]
    unfold input45Actual
    split_ifs with h
    · have hs := hsquare (⟨k.val, h⟩ : Fin 3)
      simp only [K45, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs 0
    · have hc := hcomm (⟨(k.val - 3) / 4, by omega⟩ : Fin 3)
      simp only [R45, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hc
      exact hc ⟨(k.val - 3) % 4, by omega⟩
  intro i
  simp only [R45, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a
  have ht := certificate45.target_dotProduct_eq_zero x hinput
    (⟨4 * i.val + a.val, by omega⟩ : Fin 12)
  change binaryRowFunctional (target45 _) x = 0 at ht
  rw [binaryLinearFunctional_ext_basis (target45_basis _)] at ht
  have hdiv : (4 * i.val + a.val) / 4 = i.val := by omega
  have hmod : (4 * i.val + a.val) % 4 = a.val := by omega
  simpa only [target45Actual, hdiv, hmod] using ht

/-- For the kernel J², square-in-J² and commuting modulo J³ force all
three square carries into J³. -/
theorem square_carry46 (x : Offsets)
    (hsquare : ∀ i, squareDisplacement i x ∈ K46)
    (hcomm : ∀ p,
      commutatorDisplacement (pairs p).1 (pairs p).2 x ∈ R46) :
    ∀ i, squareDisplacement i x ∈ R46 := by
  have hinput (k : Fin 33) : dotProduct (input46 k) x = 0 := by
    change binaryRowFunctional (input46 k) x = 0
    rw [binaryLinearFunctional_ext_basis (input46_basis k)]
    unfold input46Actual
    split_ifs with h
    · have hs := hsquare (⟨k.val / 4, by omega⟩ : Fin 3)
      simp only [K46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨k.val % 4, by omega⟩
    · have hc := hcomm (⟨(k.val - 12) / 7, by omega⟩ : Fin 3)
      simp only [R46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hc
      exact hc ⟨(k.val - 12) % 7, by omega⟩
  intro i
  simp only [R46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a
  have ht := certificate46.target_dotProduct_eq_zero x hinput
    (⟨7 * i.val + a.val, by omega⟩ : Fin 21)
  change binaryRowFunctional (target46 _) x = 0 at ht
  rw [binaryLinearFunctional_ext_basis (target46_basis _)] at ht
  have hdiv : (7 * i.val + a.val) / 7 = i.val := by omega
  have hmod : (7 * i.val + a.val) % 7 = a.val := by omega
  simpa only [target46Actual, hdiv, hmod] using ht

end SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry
