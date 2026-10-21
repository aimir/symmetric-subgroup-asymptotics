import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! A binary symplectic order-three rotation and a disjoint short root
can be separated by powers. Three conjugate short-root matrices then
recover a pure long root. These sparse identities hold in every rank at
least three; in particular they retain the formerly exceptional rank3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRotationArrays
open Matrix CFSGSymplecticSerreMatrices
variable {K : Type*} [CommRing K] [CharP K 2]

def paired {r : ℕ} : Index r→Index r
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

def longArray {r : ℕ} (a : Index r) : Mat K r :=
  1+Matrix.single a (paired a) 1

def shortArray {r : ℕ} (a b : Index r) : Mat K r :=
  1+Matrix.single a b 1+Matrix.single (paired b) (paired a) 1

def coord0 (r : ℕ) (hr : 3≤r) : Index r := Sum.inl ⟨0,by omega⟩
def coord1 (r : ℕ) (hr : 3≤r) : Index r := Sum.inl ⟨1,by omega⟩
def coord2 (r : ℕ) (hr : 3≤r) : Index r := Sum.inl ⟨2,by omega⟩

def rotationArray (r : ℕ) (hr : 3≤r) : Mat K r :=
  longArray (coord0 r hr)*longArray (paired (coord0 r hr))

def pairArray (r : ℕ) (hr : 3≤r) : Mat K r :=
  rotationArray r hr*shortArray (coord1 r hr) (coord2 r hr)

theorem rotation_cube (r : ℕ) (hr : 3≤r) :
    rotationArray (K:=K) r hr^3=1 := by
  simp [rotationArray,longArray,coord0,paired,pow_succ,add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

theorem short_twelve_square (r : ℕ) (hr : 3≤r) :
    shortArray (K:=K) (coord1 r hr) (coord2 r hr)^2=1 := by
  simp [shortArray,coord1,coord2,paired,pow_two,add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

theorem rotation_commutes_short_twelve (r : ℕ) (hr : 3≤r) :
    Commute (rotationArray (K:=K) r hr) (shortArray (coord1 r hr) (coord2 r hr)) := by
  change rotationArray r hr*shortArray (coord1 r hr) (coord2 r hr)=
    shortArray (coord1 r hr) (coord2 r hr)*rotationArray (K:=K) r hr
  simp [rotationArray,longArray,shortArray,coord0,coord1,coord2,paired,
    add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

theorem pair_cube (r : ℕ) (hr : 3≤r) :
    pairArray (K:=K) r hr^3=shortArray (coord1 r hr) (coord2 r hr) := by
  rw [pairArray,(rotation_commutes_short_twelve r hr).mul_pow,rotation_cube,one_mul]
  calc
    shortArray (K:=K) (coord1 r hr) (coord2 r hr)^3=
        shortArray (coord1 r hr) (coord2 r hr)^2*shortArray (coord1 r hr) (coord2 r hr) :=
      pow_succ _ 2
    _=_ := by rw [short_twelve_square,one_mul]

theorem pair_four (r : ℕ) (hr : 3≤r) :
    pairArray (K:=K) r hr^4=rotationArray r hr := by
  rw [pairArray,(rotation_commutes_short_twelve r hr).mul_pow]
  have hs : shortArray (K:=K) (coord1 r hr) (coord2 r hr)^4=1 := by
    rw [show 4=2*2 from rfl,pow_mul,short_twelve_square,one_pow]
  rw [hs,mul_one,show 4=3+1 from rfl,pow_succ,rotation_cube,one_mul]

theorem rotated_short_once (r : ℕ) (hr : 3≤r) :
    rotationArray (K:=K) r hr*shortArray (coord0 r hr) (coord1 r hr)*rotationArray r hr^2=
      shortArray (paired (coord0 r hr)) (coord1 r hr) := by
  simp [rotationArray,longArray,shortArray,coord0,coord1,paired,
    pow_two,add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

theorem rotated_short_twice (r : ℕ) (hr : 3≤r) :
    rotationArray (K:=K) r hr^2*shortArray (coord0 r hr) (coord1 r hr)*rotationArray r hr=
      1+Matrix.single (coord0 r hr) (coord1 r hr) 1+
        Matrix.single (paired (coord1 r hr)) (paired (coord0 r hr)) 1+
        Matrix.single (paired (coord0 r hr)) (coord1 r hr) 1+
        Matrix.single (paired (coord1 r hr)) (coord0 r hr) 1 := by
  simp [rotationArray,longArray,shortArray,coord0,coord1,paired,
    pow_two,add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

theorem recover_long (r : ℕ) (hr : 3≤r) :
    (rotationArray (K:=K) r hr^2*shortArray (coord0 r hr) (coord1 r hr)*rotationArray r hr)*
      shortArray (coord0 r hr) (coord1 r hr)*
      (rotationArray r hr*shortArray (coord0 r hr) (coord1 r hr)*rotationArray r hr^2)=
      longArray (paired (coord1 r hr)) := by
  rw [rotated_short_once,rotated_short_twice]
  simp [longArray,shortArray,coord0,coord1,paired,add_mul,mul_add,Fin.ext_iff] <;>
    (ext i j; simp only [Matrix.add_apply,Matrix.one_apply]; ring_nf <;> try simp)

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRotationArrays
