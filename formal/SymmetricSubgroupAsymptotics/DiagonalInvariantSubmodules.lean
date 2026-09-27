import SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection

/-!
# Exact invariant-submodule classification by distinct coordinate isotypes

The parameters are the original scalar functions. An invariant submodule
is exactly a family of arbitrary submodules on the coordinate fibres of
distinct scalar labels. Restriction and extension by zero give explicit
inverse maps. Coordinates with the same label are never separated into
independent one-dimensional factors.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

open DiagonalIsotypeProjection

variable {k ι J : Type*} [Field k] [Fintype ι] (scalar : ι → J → k)

abbrev Label := CharacterLabel scalar
abbrev Coordinate (a : Label scalar) := {i : ι // scalar i=a.1}

def restriction (a : Label scalar) : (ι → k) →ₗ[k] (Coordinate scalar a → k) where
  toFun v i := v i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extension (a : Label scalar) : (Coordinate scalar a → k) →ₗ[k] (ι → k) where
  toFun w i := if hi : scalar i=a.1 then w ⟨i,hi⟩ else 0
  map_add' w w' := by
    funext i
    by_cases hi : scalar i=a.1 <;> simp [hi]
  map_smul' c w := by
    funext i
    by_cases hi : scalar i=a.1 <;> simp [hi]

@[simp] theorem restriction_extension (a : Label scalar) (w : Coordinate scalar a → k) :
    restriction scalar a (extension scalar a w)=w := by
  funext i
  simp [restriction,extension,i.2]

theorem extension_restriction (a : Label scalar) (v : ι → k) :
    extension scalar a (restriction scalar a v)=isotypeProjection scalar a v := by
  funext i
  by_cases hi : scalar i=a.1 <;> simp [restriction,extension,hi]

theorem restriction_extension_of_ne (a b : Label scalar) (hab : a≠b)
    (w : Coordinate scalar b → k) : restriction scalar a (extension scalar b w)=0 := by
  funext i
  have hi : scalar i.1≠b.1 := fun h => hab (Subtype.ext (i.2.symm.trans h))
  simp [restriction,extension,hi]

theorem restriction_diagonal (a : Label scalar) (g : J) (v : ι → k) :
    restriction scalar a (diagonalOperator scalar g v)=a.1 g • restriction scalar a v := by
  funext i
  change scalar i.1 g * v i.1 = a.1 g * v i.1
  rw [i.2]

/-- Actual stable submodules, with all original coordinates retained. -/
def Stable := {K : Submodule k (ι → k) //
  ∀ g v, v∈K → diagonalOperator scalar g v∈K}

def encode (K : Stable scalar) (a : Label scalar) : Submodule k (Coordinate scalar a → k) :=
  K.1.comap (extension scalar a)

def assembled (L : ∀ a : Label scalar, Submodule k (Coordinate scalar a → k)) :
    Submodule k (ι → k) := ⨅ a, (L a).comap (restriction scalar a)

@[simp] theorem mem_assembled
    (L : ∀ a : Label scalar, Submodule k (Coordinate scalar a → k)) (v : ι → k) :
    v∈assembled scalar L ↔ ∀ a, restriction scalar a v∈L a := by
  simp [assembled,Submodule.mem_iInf]

def decode (L : ∀ a : Label scalar, Submodule k (Coordinate scalar a → k)) : Stable scalar :=
  ⟨assembled scalar L,by
    intro g v hv
    apply (mem_assembled scalar L _).mpr
    intro a
    rw [restriction_diagonal]
    exact (L a).smul_mem _ ((mem_assembled scalar L v).mp hv a)⟩

theorem encode_decode
    (L : ∀ a : Label scalar, Submodule k (Coordinate scalar a → k)) :
    encode scalar (decode scalar L)=L := by
  funext a
  apply Submodule.ext
  intro w
  change extension scalar a w∈assembled scalar L ↔ w∈L a
  rw [mem_assembled]
  constructor
  · intro h
    simpa only [restriction_extension] using h a
  · intro hw b
    by_cases hb : b=a
    · subst b
      simpa only [restriction_extension] using hw
    · rw [restriction_extension_of_ne scalar b a hb]
      exact (L b).zero_mem

theorem decode_encode (K : Stable scalar) : decode scalar (encode scalar K)=K := by
  apply Subtype.ext
  apply Submodule.ext
  intro v
  change v∈assembled scalar (encode scalar K) ↔ v∈K.1
  rw [mem_assembled]
  have he : (∀ a, restriction scalar a v∈encode scalar K a) ↔
      ∀ a, isotypeProjection scalar a v∈K.1 := by
    apply forall_congr'
    intro a
    change extension scalar a (restriction scalar a v)∈K.1 ↔ _
    rw [extension_restriction]
  rw [he]
  exact (mem_iff_isotypeProjection_mem scalar K.1 K.2 v).symm

/-- No choices of bases, multiplicity divisors or independent source
characters occur in this exact parameter equivalence. -/
def equiv : Stable scalar ≃ (∀ a : Label scalar, Submodule k (Coordinate scalar a → k)) where
  toFun := encode scalar
  invFun := decode scalar
  left_inv := decode_encode scalar
  right_inv := encode_decode scalar

def FullCoordinates {I : Type*} (K : Submodule k (I → k)) : Prop :=
  ∀ i, Function.Surjective (fun v : K => v.1 i)

theorem fullCoordinates_iff (K : Stable scalar) :
    FullCoordinates K.1 ↔ ∀ a, FullCoordinates (encode scalar K a) := by
  constructor
  · intro h a i c
    obtain ⟨v,hv⟩ := h i.1 c
    have hm : restriction scalar a v.1∈encode scalar K a := by
      change extension scalar a (restriction scalar a v.1)∈K.1
      rw [extension_restriction]
      exact isotypeProjection_mem scalar K.1 K.2 a v.1 v.2
    exact ⟨⟨restriction scalar a v.1,hm⟩,hv⟩
  · intro h i c
    let a : Label scalar := coordinateLabel scalar i
    let j : Coordinate scalar a := ⟨i,rfl⟩
    obtain ⟨w,hw⟩ := h a j c
    refine ⟨⟨extension scalar a w.1,w.2⟩,?_⟩
    change (extension scalar a w.1) i=c
    have he := congrFun (restriction_extension scalar a w.1) j
    exact he.trans hw

end SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

end

