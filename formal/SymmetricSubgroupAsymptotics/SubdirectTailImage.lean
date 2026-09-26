import SymmetricSubgroupAsymptotics.FullSubdirectGoursat

/-! The literal complete tail image of an original product subgroup.
Restricting the second coordinate to this actual image gives a concrete
group equivalence and a full subdirect subgroup. No tail is replaced by
an abstract isomorphism type or assumed to be a full direct product.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace SubdirectTailImage

variable {A B : Type*} [Group A] [Group B]

def tail (H : Subgroup (A × B)) : Subgroup B := H.map (MonoidHom.snd A B)

def inclusion (L : Subgroup B) : A × L →* A × B where
  toFun x := (x.1,(x.2 : B))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inclusion_injective (L : Subgroup B) : Function.Injective (inclusion (A := A) L) := by
  intro x y he
  apply Prod.ext
  · exact congrArg (fun p : A × B => p.1) he
  · exact Subtype.ext (congrArg (fun p : A × B => p.2) he)

def core (H : Subgroup (A × B)) : Subgroup (A × tail H) :=
  H.comap (inclusion (tail H))

/-- Both directions retain the original first coordinate and the original
second-coordinate value; only its membership in the actual image is bundled. -/
def equiv (H : Subgroup (A × B)) : H ≃* core H where
  toFun h := ⟨(h.1.1,⟨h.1.2,⟨h.1,h.2,rfl⟩⟩),h.2⟩
  invFun h := ⟨inclusion (tail H) h.1,h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem equiv_fst (H : Subgroup (A × B)) (h : H) :
    ((equiv H h : core H) : A × tail H).1 = h.1.1 := rfl

@[simp] theorem equiv_snd (H : Subgroup (A × B)) (h : H) :
    ((((equiv H h : core H) : A × tail H).2) : B) = h.1.2 := rfl

/-- Mapping the core back through its literal coordinate inclusion
recovers the entire original subgroup. -/
theorem core_map (H : Subgroup (A × B)) :
    (core H).map (inclusion (tail H)) = H := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨(equiv H ⟨x,hx⟩).1,(equiv H ⟨x,hx⟩).2,rfl⟩

theorem core_fst_surjective (H : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ H.subtype)) :
    Function.Surjective (Prod.fst ∘ (core H).subtype) := by
  intro a
  obtain ⟨h,hh⟩ := hA a
  exact ⟨equiv H h,hh⟩

theorem core_snd_surjective (H : Subgroup (A × B)) :
    Function.Surjective (Prod.snd ∘ (core H).subtype) := by
  rintro ⟨b,hb⟩
  obtain ⟨h,hh,he⟩ := hb
  exact ⟨equiv H ⟨h,hh⟩,Subtype.ext he⟩

/-- First fullness and the exact image construction give the complete
full-subdirect object expected by the marked peel theorem. -/
def full (H : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ H.subtype)) :
    FullSubdirectGoursat.Full A (tail H) :=
  ⟨core H,core_fst_surjective H hA,core_snd_surjective H⟩

/-- The first axis remains the identical subgroup of the original A. -/
theorem core_axis (H : Subgroup (A × B)) : (core H).goursatFst = H.goursatFst := by
  ext a
  rw [Subgroup.mem_goursatFst,Subgroup.mem_goursatFst]
  rfl

/-- Every full original tail coordinate remains full on the literal
tail image. Applying this to each displayed coordinate retains word fullness. -/
theorem tail_coordinate_surjective (H : Subgroup (A × B)) {C : Type*} (π : B → C)
    (hπ : Function.Surjective (π ∘ Prod.snd ∘ H.subtype)) :
    Function.Surjective (π ∘ (tail H).subtype) := by
  intro c
  obtain ⟨h,hh⟩ := hπ c
  exact ⟨⟨h.1.2,⟨h.1,h.2,rfl⟩⟩,hh⟩

abbrev FirstFull (A B : Type*) [Group A] [Group B] :=
  {H : Subgroup (A × B) // Function.Surjective (Prod.fst ∘ H.subtype)}

/-- The complete tail subgroup is recorded before peeling, and therefore
is available once for every later attachment or original survival test. -/
def code (H : FirstFull A B) :
    Σ L : Subgroup B, FullSubdirectGoursat.Full A L :=
  ⟨tail H.1,full H.1 H.2⟩

def decode (d : Σ L : Subgroup B, FullSubdirectGoursat.Full A L) : Subgroup (A × B) :=
  d.2.1.map (inclusion d.1)

@[simp] theorem decode_code (H : FirstFull A B) : decode (code H) = H.1 := core_map H.1

/-- Distinct original subgroups cannot share the same actual tail and
same full core. This is the injective family bridge for finite-word induction. -/
theorem code_injective : Function.Injective (code (A := A) (B := B)) := by
  intro H K h
  apply Subtype.ext
  exact (decode_code H).symm.trans ((congrArg decode h).trans (decode_code K))

end SubdirectTailImage
end SymmetricSubgroupAsymptotics
