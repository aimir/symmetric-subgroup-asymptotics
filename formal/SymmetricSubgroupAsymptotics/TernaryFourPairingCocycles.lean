import SymmetricSubgroupAsymptotics.TernaryFourCocycleImages
import SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-! The actual A4 character and S4 pairing action give the two diagonal
cocycles used by the retained affine generators. The S4 cocycle is read
in the ternary chart [2,0,1] on the three pairings; its scalar is proved
equal to the actual sign character using the two displayed S4 generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourPairingCocycles

open TernaryFourBlockPermutationGenerators TernaryFourCocycleImages

abbrev A4 := alternatingGroup (Fin 4)
abbrev alternatingBlocks : A4 →* Equiv.Perm (Fin 4) := (alternatingGroup (Fin 4)).subtype
abbrev symmetricBlocks := MonoidHom.id (Equiv.Perm (Fin 4))

def alternating : Cocycle (1 : A4 →* (ZMod 3)ˣ) where
  value g := (NaturalA4ScalarFourHead.top g).toAdd
  one := by
    rw [map_one]
    rfl
  mul g h := by
    change (NaturalA4ScalarFourHead.top (g*h)).toAdd =
      (NaturalA4ScalarFourHead.top g).toAdd + 1*(NaturalA4ScalarFourHead.top h).toAdd
    rw [map_mul,one_mul]
    rfl

def label (i : Fin 3) : ZMod 3 := (i.val : ZMod 3)+2

def scalarThree : Equiv.Perm (Fin 3) →* (ZMod 3)ˣ :=
  (Units.map (Int.castRingHom (ZMod 3)).toMonoidHom).comp Equiv.Perm.sign

/-- A local identity on the three labels, not a generated-group census. -/
theorem label_action : ∀ (g : Equiv.Perm (Fin 3)) (i : Fin 3),
    label (g i) = label (g 1) + (scalarThree g : ZMod 3)*label i := by
  decide +kernel

theorem scalar_pairing : scalarThree.comp NaturalS4.pairing = TernaryFourSignedAugmentation.scalar := by
  apply MonoidHom.eq_of_eqOn_dense symmetric_generated
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> decide +kernel

def symmetric : Cocycle TernaryFourSignedAugmentation.scalar where
  value g := label (NaturalS4.pairing g 1)
  one := by
    rw [NaturalS4.pairing.map_one]
    decide +kernel
  mul g h := by
    rw [NaturalS4.pairing.map_mul]
    change label (NaturalS4.pairing g (NaturalS4.pairing h 1)) = _
    rw [label_action]
    have hs : scalarThree (NaturalS4.pairing g) = TernaryFourSignedAugmentation.scalar g :=
      congrArg (fun f : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ => f g) scalar_pairing
    rw [hs]

def alternatingFirst : A4 := ⟨a,a_even⟩
def alternatingSecond : A4 := ⟨b,b_even⟩
def kleinFirst : A4 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3,by
  change Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 1
  decide +kernel⟩
def kleinSecond : A4 := ⟨Equiv.swap 0 2 * Equiv.swap 1 3,by
  change Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) = 1
  decide +kernel⟩

theorem alternating_pair_generated :
    Subgroup.closure ({alternatingFirst,alternatingSecond} : Set A4) = ⊤ := by
  let K := Subgroup.closure ({alternatingFirst,alternatingSecond} : Set A4)
  have hmap : alternatingGroup (Fin 4) ≤ K.map alternatingBlocks := by
    apply alternating_generated.ge.trans
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨alternatingFirst,Subgroup.subset_closure (by simp),rfl⟩
    · exact ⟨alternatingSecond,Subgroup.subset_closure (by simp),rfl⟩
  apply top_unique
  intro g _
  obtain ⟨h,hh,he⟩ := hmap g.2
  have he' : h = g := Subtype.ext he
  rwa [← he']

theorem alternating_of_klein_cycle (K : Subgroup A4)
    (hk : kleinFirst ∈ K) (hb : alternatingSecond ∈ K) : K = ⊤ := by
  have ha : alternatingFirst ∈ K := by
    have he : alternatingFirst = kleinFirst * alternatingSecond⁻¹ := by
      apply Subtype.ext
      decide +kernel
    rw [he]
    exact K.mul_mem hk (K.inv_mem hb)
  apply top_unique
  rw [← alternating_pair_generated]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ha
  · exact hb

theorem symmetric_of_klein_swaps (K : Subgroup (Equiv.Perm (Fin 4)))
    (hk : kleinFirst.1 ∈ K) (h01 : Equiv.swap 0 1 ∈ K) (h12 : Equiv.swap 1 2 ∈ K) : K = ⊤ := by
  have hs : s ∈ K := by
    have he : s = kleinFirst.1 * Equiv.swap 0 1 := by decide +kernel
    rw [he]
    exact K.mul_mem hk h01
  have hc : c ∈ K := by
    have he : c = Equiv.swap 0 1 * Equiv.swap 1 2 * s := by decide +kernel
    rw [he]
    exact K.mul_mem (K.mul_mem h01 h12) hs
  apply top_unique
  rw [← symmetric_generated]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hc
  · exact hs

end SymmetricSubgroupAsymptotics.TernaryFourPairingCocycles

end
