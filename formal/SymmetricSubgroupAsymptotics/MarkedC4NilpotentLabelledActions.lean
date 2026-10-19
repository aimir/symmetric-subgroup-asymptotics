import SymmetricSubgroupAsymptotics.MarkedC4NilpotentOriginalLabels
import SymmetricSubgroupAsymptotics.MarkedC4ActiveCoordinateLabels
import SymmetricSubgroupAsymptotics.MarkedC4NilpotentPointGridEquivariance

/-! Uniform finite-alphabet actions on the actual original label code.
Their equivariance is derived from the constructed physical grid. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentLabelledActions
open NilpotentSylowFactors NilpotentPermutationGrid NilpotentCompressedImages
local instance activeFintype {I : Type} [Fintype I]
    (F : I → Type) [∀ i,Fintype (F i)] : Fintype (PhysicalGridLabels.Active F) :=
  ActiveCoordinateLabels.instFintypeActive F
variable {b : ℕ} (K : Subgroup (PermutationGroup b)) [Group.IsNilpotent K]
local instance : Fintype (OrbitIndex K (Fin b)) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (BinaryFiber K (Fin b) ω) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (OddFiber K (Fin b) ω) := Fintype.ofFinite _

private theorem binary_bound :
    Fintype.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b)))≤b := by
  have h := physical_budget K (Fin b)
  have ha := (Nat.le_add_right (Nat.card (BinarySupport K (Fin b)))
    (Nat.card (OddSupport K (Fin b)))).trans h
  change Nat.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b))) ≤ Nat.card (Fin b) at ha
  simpa only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin] using ha
private theorem odd_bound :
    Fintype.card (PhysicalGridLabels.Active (OddFiber K (Fin b)))≤b := by
  have h := physical_budget K (Fin b)
  have hd := (Nat.le_add_left (Nat.card (OddSupport K (Fin b)))
    (Nat.card (BinarySupport K (Fin b)))).trans h
  change Nat.card (PhysicalGridLabels.Active (OddFiber K (Fin b))) ≤ Nat.card (Fin b) at hd
  simpa only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin] using hd

def binary : K →* Equiv.Perm (Fin (b+1)) :=
  (ActiveCoordinateLabels.action (BinaryFiber K (Fin b)) (binary_bound K)).comp
    ((MonoidHom.fst _ _).comp (equiv K).toMonoidHom)
def odd : K →* Equiv.Perm (Fin (b+1)) :=
  (ActiveCoordinateLabels.action (OddFiber K (Fin b)) (odd_bound K)).comp
    ((MonoidHom.snd _ _).comp (equiv K).toMonoidHom)

def move (p o : Equiv.Perm (Fin (b+1)))
    (z : Fin (b+1) × Fin (b+1) × Fin (b+1)) := (z.1,p z.2.1,o z.2.2)

/-- The finite labels intertwine the ORIGINAL literal permutation. -/
theorem code_equivariant (g : K) (x : Fin b) :
    NilpotentOriginalLabels.code K (g.val x)=
      move (binary K g) (odd K g) (NilpotentOriginalLabels.code K x) := by
  unfold NilpotentOriginalLabels.code
  have hgrid := NilpotentPointGridEquivariance.equivariant K (Fin b) g x
  change pointGrid K (Fin b) (g.val x)=_ at hgrid
  rw [hgrid]
  let z := pointGrid K (Fin b) x
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext
      change PhysicalGridLabels.activeLabel (BinaryFiber K (Fin b)) z.1
          ((equiv K g).1 • z.2.1)=_
      have h := ActiveCoordinateLabels.equivariant (BinaryFiber K (Fin b))
        (binary_bound K) (equiv K g).1 z.1 z.2.1
      have hl : ActiveCoordinateLabels.label (BinaryFiber K (Fin b)) (binary_bound K)
          z.1 z.2.1 =
          (NilpotentOriginalLabels.code K x).2.1 := by
        apply Fin.ext
        exact ActiveCoordinateLabels.label_val _ _ _ _
      rw [hl] at h
      exact (ActiveCoordinateLabels.label_val _ _ _ _).symm.trans (congrArg Fin.val h)
    · apply Fin.ext
      change PhysicalGridLabels.activeLabel (OddFiber K (Fin b)) z.1
          ((equiv K g).2 • z.2.2)=_
      have h := ActiveCoordinateLabels.equivariant (OddFiber K (Fin b))
        (odd_bound K) (equiv K g).2 z.1 z.2.2
      have hl : ActiveCoordinateLabels.label (OddFiber K (Fin b)) (odd_bound K)
          z.1 z.2.2 =
          (NilpotentOriginalLabels.code K x).2.2 := by
        apply Fin.ext
        exact ActiveCoordinateLabels.label_val _ _ _ _
      rw [hl] at h
      exact (ActiveCoordinateLabels.label_val _ _ _ _).symm.trans (congrArg Fin.val h)

/-- The two range elements can be realized simultaneously by one original
source element, using the actual Sylow factor equivalence. -/
theorem exists_pair (p : (binary K).range) (o : (odd K).range) :
    ∃ g : K, binary K g=p.val ∧ odd K g=o.val := by
  obtain ⟨gp,hp⟩ := p.property
  obtain ⟨go,ho⟩ := o.property
  refine ⟨(equiv K).symm ((equiv K gp).1,(equiv K go).2),?_,?_⟩
  · change ActiveCoordinateLabels.action _ _
      ((equiv K) ((equiv K).symm ((equiv K gp).1,(equiv K go).2))).1=p.val
    rw [(equiv K).apply_symm_apply]
    exact hp
  · change ActiveCoordinateLabels.action _ _
      ((equiv K) ((equiv K).symm ((equiv K gp).1,(equiv K go).2))).2=o.val
    rw [(equiv K).apply_symm_apply]
    exact ho

/-- This is actual subgroup recovery, not an assumed injective encoding. -/
theorem recover (f : Equiv.Perm (Fin b)) : f∈K ↔
    ∃ (p : (binary K).range) (o : (odd K).range), ∀ x : Fin b,
      NilpotentOriginalLabels.code K (f x)=
        move p o (NilpotentOriginalLabels.code K x) := by
  constructor
  · intro hf
    let g : K := ⟨f,hf⟩
    exact ⟨⟨binary K g,⟨g,rfl⟩⟩,⟨odd K g,⟨g,rfl⟩⟩,code_equivariant K g⟩
  · rintro ⟨p,o,hf⟩
    obtain ⟨g,hp,ho⟩ := exists_pair K p o
    have he : f=(g : Equiv.Perm (Fin b)) := by
      apply Equiv.ext
      intro x
      apply NilpotentOriginalLabels.code_injective K
      rw [hf x,code_equivariant K g x,hp,ho]
    exact he.symm ▸ g.property

/-- Equal range subgroups and equal original-label maps recover equal
original source subgroups, regardless of their Sylow/chart choices. -/
theorem source_eq {L : Subgroup (PermutationGroup b)} [Group.IsNilpotent L]
    (hp : (binary K).range=(binary L).range)
    (ho : (odd K).range=(odd L).range)
    (hc : NilpotentOriginalLabels.code K=NilpotentOriginalLabels.code L) : K=L := by
  ext f
  rw [recover K f,recover L f]
  constructor
  · rintro ⟨p,o,h⟩
    refine ⟨⟨p.val,hp ▸ p.property⟩,⟨o.val,ho ▸ o.property⟩,?_⟩
    intro x
    simpa only [hc] using h x
  · rintro ⟨p,o,h⟩
    refine ⟨⟨p.val,hp.symm ▸ p.property⟩,⟨o.val,ho.symm ▸ o.property⟩,?_⟩
    intro x
    simpa only [hc] using h x
def pairMap : K →* (binary K).range × (odd K).range :=
  (binary K).rangeRestrict.prod (odd K).rangeRestrict

theorem pairMap_surjective : Function.Surjective (pairMap K) := by
  rintro ⟨p,o⟩
  obtain ⟨g,hp,ho⟩ := exists_pair K p o
  exact ⟨g,Prod.ext (Subtype.ext hp) (Subtype.ext ho)⟩

theorem pairMap_injective : Function.Injective (pairMap K) := by
  apply (MonoidHom.ker_eq_bot_iff (pairMap K)).mp
  apply le_antisymm _ bot_le
  intro g hg
  have h := MonoidHom.mem_ker.mp hg
  have hp : binary K g=1 := congrArg
    (fun z : (binary K).range × (odd K).range => (z.1 : Equiv.Perm (Fin (b+1)))) h
  have ho : odd K g=1 := congrArg
    (fun z : (binary K).range × (odd K).range => (z.2 : Equiv.Perm (Fin (b+1)))) h
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply NilpotentOriginalLabels.code_injective K
  rw [code_equivariant K g x,hp,ho]
  rfl

def rangeEquiv : K ≃* (binary K).range × (odd K).range :=
  MulEquiv.ofBijective (pairMap K) ⟨pairMap_injective K,pairMap_surjective K⟩

theorem odd_range_coprime_four : Nat.Coprime (Nat.card (odd K).range) 4 := by
  let f : OddFactor K →* (odd K).range := (odd K).rangeRestrict.comp
    ((equiv K).symm.toMonoidHom.comp (MonoidHom.inr (Binary K) (OddFactor K)))
  have hf : Function.Surjective f := by
    rintro ⟨o,ho⟩
    obtain ⟨g,rfl⟩ := ho
    refine ⟨(equiv K g).2,Subtype.ext ?_⟩
    change ActiveCoordinateLabels.action (OddFiber K (Fin b)) (odd_bound K)
      ((equiv K) ((equiv K).symm (1,(equiv K g).2))).2 =
      ActiveCoordinateLabels.action (OddFiber K (Fin b)) (odd_bound K) (equiv K g).2
    rw [(equiv K).apply_symm_apply]
  exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_surjective f hf)
    (odd_card_coprime_four K)

theorem hom_card_le_binary_range :
    Nat.card (K →* Multiplicative (ZMod 4))≤
      Nat.card ((binary K).range →* Multiplicative (ZMod 4)) :=
  CoprimeProductCharacters.card_hom_le_of_split (rangeEquiv K) (odd_range_coprime_four K)

private theorem action_fixes_outside {I : Type} [Fintype I]
    (F : I → Type) [∀ i,Fintype (F i)]
    {H : Type} [Group H] [∀ i,MulAction H (F i)]
    (hcard : Fintype.card (PhysicalGridLabels.Active F)≤b)
    (g : H) (x : Fin (b+1))
    (hx : x.val=0 ∨ Fintype.card (PhysicalGridLabels.Active F)<x.val) :
    ActiveCoordinateLabels.action F hcard g x=x := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  have hv := congrArg Fin.val hz
  change (Fintype.equivFin (PhysicalGridLabels.Active F) z).val+1=x.val at hv
  have hb := (Fintype.equivFin (PhysicalGridLabels.Active F) z).isLt
  rcases hx with hx | hx <;> omega

theorem binary_support (g : K) (x : Fin (b+1))
    (hx : x.val=0 ∨ Nat.card (BinarySupport K (Fin b))<x.val) : binary K g x=x := by
  apply action_fixes_outside (BinaryFiber K (Fin b)) (binary_bound K) (equiv K g).1 x
  change x.val=0 ∨ Nat.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b)))<x.val at hx
  simpa only [Nat.card_eq_fintype_card] using hx

theorem odd_support (g : K) (x : Fin (b+1))
    (hx : x.val=0 ∨ Nat.card (OddSupport K (Fin b))<x.val) : odd K g x=x := by
  apply action_fixes_outside (OddFiber K (Fin b)) (odd_bound K) (equiv K g).2 x
  change x.val=0 ∨ Nat.card (PhysicalGridLabels.Active (OddFiber K (Fin b)))<x.val at hx
  simpa only [Nat.card_eq_fintype_card] using hx

theorem binary_range_isPGroup : IsPGroup 2 (binary K).range := by
  let f : Binary K →* (binary K).range := (binary K).rangeRestrict.comp
    ((equiv K).symm.toMonoidHom.comp (MonoidHom.inl (Binary K) (OddFactor K)))
  have hf : Function.Surjective f := by
    rintro ⟨p,hp⟩
    obtain ⟨g,rfl⟩ := hp
    refine ⟨(equiv K g).1,Subtype.ext ?_⟩
    change ActiveCoordinateLabels.action (BinaryFiber K (Fin b)) (binary_bound K)
      ((equiv K) ((equiv K).symm ((equiv K g).1,1))).1 =
      ActiveCoordinateLabels.action (BinaryFiber K (Fin b)) (binary_bound K) (equiv K g).1
    rw [(equiv K).apply_symm_apply]
  exact (binary_isPGroup K).of_surjective f hf

end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentLabelledActions
