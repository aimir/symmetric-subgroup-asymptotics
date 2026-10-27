import SymmetricSubgroupAsymptotics.FullSubdirectGoursat
import Mathlib.GroupTheory.Subgroup.Simple

/-! A lossless cover of every subgroup with normal simple-coordinate
images by its LITERAL active support and complete restricted subdirect.
All inactive coordinates are proved zero before they are forgotten.
No transitivity or one-orbit assertion is used, so multiple minimal
normal socle orbits are preserved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCover

variable {I : Type} (S : I → Type) [∀ i,Group (S i)] [∀ i,IsSimpleGroup (S i)]

def coordinate (H : Subgroup (∀ i,S i)) (i : I) : H →* S i :=
  (Pi.evalMonoidHom S i).comp H.subtype

abbrev Family := {H : Subgroup (∀ i,S i) // ∀ i,(coordinate S H i).range.Normal}

def support (H : Subgroup (∀ i,S i)) : Set I :=
  {i | Function.Surjective (coordinate S H i)}

def restriction (s : Set I) : (∀ i,S i) →* (∀ i : s,S i.val) where
  toFun f i := f i.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem outside_support_eq_one (H : Family S) (i : I) (hi : i∉support S H.val)
    (h : H.val) : h.val i=1 := by
  rcases (H.property i).eq_bot_or_eq_top with hb | ht
  · have hm : coordinate S H.val i h∈(coordinate S H.val i).range := ⟨h,rfl⟩
    rwa [hb,Subgroup.mem_bot] at hm
  · exact (hi (MonoidHom.range_eq_top.mp ht)).elim

abbrev FullOn (s : Set I) :=
  {K : Subgroup (∀ i : s,S i.val) //
    ∀ i : s,Function.Surjective (fun k : K => k.val i)}

def activeImage (H : Family S) : FullOn S (support S H.val) := by
  refine ⟨H.val.map (restriction S (support S H.val)),?_⟩
  intro i t
  obtain ⟨h,hh⟩ := i.property t
  exact ⟨⟨restriction S (support S H.val) h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

def code (H : Family S) : Σ s : Set I,FullOn S s :=
  ⟨support S H.val,activeImage S H⟩

def decode (s : Set I) (K : Subgroup (∀ i : s,S i.val)) : Subgroup (∀ i,S i) where
  carrier := {f | restriction S s f∈K ∧ ∀ i,i∉s → f i=1}
  one_mem' := ⟨K.one_mem,fun _ _ => rfl⟩
  mul_mem' := by
    intro f g hf hg
    refine ⟨K.mul_mem hf.1 hg.1,?_⟩
    intro i hi
    change f i*g i=1
    rw [hf.2 i hi,hg.2 i hi,one_mul]
  inv_mem' := by
    intro f hf
    refine ⟨K.inv_mem hf.1,?_⟩
    intro i hi
    change (f i)⁻¹=1
    rw [hf.2 i hi,inv_one]

theorem decode_code (H : Family S) : decode S (code S H).1 (code S H).2.val=H.val := by
  ext f
  constructor
  · intro hf
    change restriction S (support S H.val) f∈
      H.val.map (restriction S (support S H.val)) ∧
        ∀ i,i∉support S H.val → f i=1 at hf
    obtain ⟨h,hh,he⟩ := hf.1
    have heq : h=f := by
      funext i
      by_cases hi : i∈support S H.val
      · exact congrFun he ⟨i,hi⟩
      · exact (outside_support_eq_one S H i hi ⟨h,hh⟩).trans (hf.2 i hi).symm
    exact heq ▸ hh
  · intro hf
    refine ⟨⟨f,hf,rfl⟩,?_⟩
    intro i hi
    exact outside_support_eq_one S H i hi ⟨f,hf⟩

theorem code_injective : Function.Injective (code S) := by
  intro H K h
  apply Subtype.ext
  exact (decode_code S H).symm.trans
    ((congrArg (fun z : Σ s : Set I,FullOn S s => decode S z.1 z.2.val) h).trans
      (decode_code S K))

end SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCover
