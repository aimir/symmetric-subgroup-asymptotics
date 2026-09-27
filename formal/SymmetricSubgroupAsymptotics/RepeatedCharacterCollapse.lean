import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Finite.Range

/-!
# Reversible deletion of repeated original coordinate characters

A subgroup of a coordinate product and a full exterior is identified
with its image after retaining one coordinate per distinct character on
that same subgroup. Expansion restores every original coordinate and
the exterior verbatim. No independent-character, finite-group or
normalizer/counting premise is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedCharacterCollapse

variable {ι C D : Type*} [Group C] [Group D]
    (B : Subgroup ((ι → C) × D))

def character (i : ι) : B →* C where
  toFun b := b.1.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev Label := Set.range (character B)

def label (i : ι) : Label B := ⟨character B i,⟨i,rfl⟩⟩

/-- Keep each distinct homomorphism on the original B once, and keep
the entire exterior coordinate without alteration. -/
def collapse : B →* ((Label B → C) × D) where
  toFun b := (fun a => a.1 b,b.1.2)
  map_one' := by
    apply Prod.ext
    · funext a
      exact a.1.map_one
    · rfl
  map_mul' b c := by
    apply Prod.ext
    · funext a
      exact a.1.map_mul b c
    · rfl

/-- Recreate all displayed coordinates, including their original
multiplicities. This map is defined on the whole smaller ambient product. -/
def expand : ((Label B → C) × D) →* ((ι → C) × D) where
  toFun y := (fun i => y.1 (label B i),y.2)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem expand_collapse (b : B) : expand B (collapse B b)=b.1 := rfl

theorem collapse_injective : Function.Injective (collapse B) := by
  intro b c h
  exact Subtype.ext (congrArg (expand B) h)

def image : Subgroup ((Label B → C) × D) := (collapse B).range

def collapseToImage : B →* image B :=
  (collapse B).codRestrict (image B) (fun b => ⟨b,rfl⟩)

theorem collapseToImage_surjective : Function.Surjective (collapseToImage B) := by
  rintro ⟨y,b,rfl⟩
  exact ⟨b,rfl⟩

def equiv : B ≃* image B :=
  MulEquiv.ofBijective (collapseToImage B)
    ⟨fun _ _ h => collapse_injective B (congrArg Subtype.val h),
      collapseToImage_surjective B⟩

@[simp] theorem equiv_original (b : B) :
    expand B (equiv B b : (Label B → C) × D)=b.1 := rfl

@[simp] theorem equiv_symm_original (b : image B) :
    ((equiv B).symm b : (ι → C) × D)=expand B b.1 := by
  obtain ⟨a,rfl⟩ := (equiv B).surjective b
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem expand_image : (image B).map (expand B)=B := by
  apply le_antisymm
  · rintro _ ⟨y,⟨b,rfl⟩,rfl⟩
    exact b.2
  · intro b hb
    exact ⟨collapse B ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩,rfl⟩

def imageCharacter (a : Label B) : image B →* C where
  toFun b := b.1.1 a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem imageCharacter_comp (a : Label B) :
    (imageCharacter B a).comp (collapseToImage B)=a.1 := rfl

/-- The retained coordinates remain distinct on the actual new image,
not merely on an isomorphic abstract replacement group. -/
theorem imageCharacter_injective : Function.Injective (imageCharacter B) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun f => f.comp (collapseToImage B)) h

theorem imageCharacter_surjective_iff (a : Label B) :
    Function.Surjective (imageCharacter B a) ↔ Function.Surjective a.1 := by
  constructor
  · intro h c
    obtain ⟨b,hb⟩ := h c
    obtain ⟨x,rfl⟩ := collapseToImage_surjective B b
    exact ⟨x,hb⟩
  · intro h c
    obtain ⟨b,hb⟩ := h c
    exact ⟨collapseToImage B b,hb⟩

theorem image_isPGroup {p : ℕ} (hB : IsPGroup p B) : IsPGroup p (image B) :=
  hB.of_equiv (equiv B)

end SymmetricSubgroupAsymptotics.RepeatedCharacterCollapse

end

