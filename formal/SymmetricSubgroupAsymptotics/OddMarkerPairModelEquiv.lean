import SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfile
import SymmetricSubgroupAsymptotics.OddMarkerBinaryContraction
import SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalBinary

/-!
# One natural marker versus one retained pair coordinate

For an arbitrary complete binary exterior profile, a single full natural
`S_3` orbit contracts bijectively to one new full `C_2` pair coordinate.
Every old pair coordinate and every other exterior projection is retained.
This is the model-level equivalence needed before comparing the original
physical normalizers `6` and `2`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OddMarkerPairModelEquiv

open RepeatedMarkerMergedProfile

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a))) (p : ℕ)

abbrev BasePoints := RepeatedMarkerMergedProfile.points Ω
abbrev BaseAction := RepeatedMarkerMergedProfile.action Ω U
abbrev BaseMultiplicity := RepeatedMarkerMergedProfile.multiplicity m p
abbrev BaseOriginal := OrbitProfileProductGroup (BaseMultiplicity m p) (BaseAction Ω U)

abbrev OddPoints := RepeatedOddMarkerPhysicalProfile.points (BasePoints Ω)
abbrev OddAction := RepeatedOddMarkerPhysicalProfile.action (BasePoints Ω) (BaseAction Ω U)
abbrev OddMultiplicity := RepeatedOddMarkerPhysicalProfile.multiplicity (BaseMultiplicity m p) 1
abbrev OddModel :=
  {K : Subgroup (Equiv.Perm (OrbitProfilePoints (OddPoints Ω) (OddMultiplicity m p))) //
    OrbitProfileFull (OddAction Ω U) 1 K}

abbrev BinaryModel := BinaryDuplicatePairProfile.Model Ω m U (p+1)

def MarkerFull {G : Type*} [Group G]
    (H : Subgroup (G × BaseOriginal Ω m U p)) : Prop :=
  H.map (MonoidHom.fst G _) = ⊤ ∧
    OrbitProfileProductFull (BaseMultiplicity m p) (BaseAction Ω U)
      (H.map (MonoidHom.snd G _))

/-- Split the unique marker coordinate from the complete old exterior. -/
def oddProductEquiv :
    OrbitProfileProductGroup (OddMultiplicity m p) (OddAction Ω U) ≃*
      OddMarkerGroup × BaseOriginal Ω m U p where
  toFun g := ((g (.inl PUnit.unit) (0 : Fin 1)).1, fun i => g (.inr i))
  invFun g i := match i with
    | .inl _ => fun _ => ⟨g.1, Subgroup.mem_top _⟩
    | .inr i => g.2 i
  left_inv g := by
    funext i j
    cases i with
    | inl i =>
        cases i
        change Fin 1 at j
        have hj : j = (0 : Fin 1) := Fin.eq_zero j
        subst j
        rfl
    | inr i => rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem oddProduct_full_iff
    (H : Subgroup (OrbitProfileProductGroup (OddMultiplicity m p) (OddAction Ω U))) :
    OrbitProfileProductFull (OddMultiplicity m p) (OddAction Ω U) H ↔
      MarkerFull Ω m U p (H.map (oddProductEquiv Ω m U p).toMonoidHom) := by
  constructor
  · intro h
    constructor
    · apply top_unique
      intro z _
      obtain ⟨g,hg⟩ := h (.inl PUnit.unit) (0 : Fin 1) ⟨z,Subgroup.mem_top _⟩
      refine Subgroup.mem_map.mpr ⟨oddProductEquiv Ω m U p g.1,
        Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩,?_⟩
      exact congrArg Subtype.val hg
    · intro i j u
      obtain ⟨g,hg⟩ := h (.inr i) j u
      exact ⟨⟨(oddProductEquiv Ω m U p g.1).2,
        Subgroup.mem_map.mpr ⟨oddProductEquiv Ω m U p g.1,
          Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩,rfl⟩⟩,hg⟩
  · rintro ⟨hfirst,htail⟩ i j u
    cases i with
    | inl i =>
      have hu : u.1 ∈
          (H.map (oddProductEquiv Ω m U p).toMonoidHom).map
            (MonoidHom.fst OddMarkerGroup (BaseOriginal Ω m U p)) := by
        rw [hfirst]
        trivial
      obtain ⟨g,hg,hgu⟩ := Subgroup.mem_map.mp hu
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hg
      refine ⟨⟨a,ha⟩,?_⟩
      apply Subtype.ext
      change Fin 1 at j
      have hj : j = (0 : Fin 1) := Fin.eq_zero j
      subst j
      change oddProductEquiv Ω m U p a = g at he
      change g.1 = u.1 at hgu
      exact (congrArg Prod.fst he).trans hgu
    | inr i =>
      obtain ⟨g,hg⟩ := htail i j u
      obtain ⟨b,hb,hbg⟩ := Subgroup.mem_map.mp g.2
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hb
      refine ⟨⟨a,ha⟩,?_⟩
      change oddProductEquiv Ω m U p a = b at he
      change b.2 = g.1 at hbg
      have hat : (oddProductEquiv Ω m U p a).2 = g.1 :=
        (congrArg Prod.snd he).trans hbg
      change (oddProductEquiv Ω m U p a).2 i j = u
      rw [hat]
      exact hg

/-- Install the contracted sign as the first occurrence of the original
critical pair action. -/
def binaryProductEquiv :
    RepeatedMarkerMergedProfile.Sign × BaseOriginal Ω m U p ≃*
      RepeatedMarkerMergedProfile.Original Ω m U (p+1) where
  toFun g i := match i with
    | .inl _ => Fin.cons (binaryMarkerLocalEquiv g.1) (g.2 (.inl PUnit.unit))
    | .inr a => g.2 (.inr a)
  invFun g := (binaryMarkerLocalEquiv.symm (g (.inl PUnit.unit) (0 : Fin (p+1))),
    fun i => match i with
      | .inl _ => fun j => g (.inl PUnit.unit) j.succ
      | .inr a => g (.inr a))
  left_inv g := by
    apply Prod.ext
    · exact binaryMarkerLocalEquiv.symm_apply_apply _
    · funext i j
      cases i <;> rfl
  right_inv g := by
    funext i j
    cases i with
    | inl i =>
      cases i
      refine Fin.cases ?_ (fun _ => rfl) j
      exact binaryMarkerLocalEquiv.apply_symm_apply _
    | inr a => rfl
  map_mul' g h := by
    funext i j
    cases i with
    | inl i =>
      cases i
      refine Fin.cases ?_ (fun _ => rfl) j
      exact binaryMarkerLocalEquiv.map_mul _ _
    | inr a => rfl

def oldIndex (i : PUnit.{1} ⊕ α) :
    Fin (BaseMultiplicity m p i) → Fin (RepeatedMarkerMergedProfile.multiplicity m (p+1) i) := by
  cases i with
  | inl i => exact Fin.succ
  | inr a => exact id

@[simp] theorem binaryProductEquiv_old
    (g : RepeatedMarkerMergedProfile.Sign × BaseOriginal Ω m U p)
    (i : PUnit.{1} ⊕ α) (j : Fin (BaseMultiplicity m p i)) :
    binaryProductEquiv Ω m U p g i (oldIndex m p i j) = g.2 i j := by
  cases i <;> rfl

theorem binaryProduct_full_iff
    (H : Subgroup (RepeatedMarkerMergedProfile.Sign × BaseOriginal Ω m U p)) :
    OrbitProfileProductFull (RepeatedMarkerMergedProfile.multiplicity m (p+1))
        (BaseAction Ω U) (H.map (binaryProductEquiv Ω m U p).toMonoidHom) ↔
      MarkerFull Ω m U p H := by
  constructor
  · intro h
    constructor
    · apply top_unique
      intro z _
      obtain ⟨g,hg⟩ := h (.inl PUnit.unit) (0 : Fin (p+1))
        (binaryMarkerLocalEquiv z)
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      refine Subgroup.mem_map.mpr ⟨a,ha,?_⟩
      apply binaryMarkerLocalEquiv.injective
      change binaryMarkerLocalEquiv a.1 = binaryMarkerLocalEquiv z
      have hh := congrArg
        (fun x => x (.inl PUnit.unit) (0 : Fin (p+1))) he
      have hh' : (binaryProductEquiv Ω m U p a) (.inl PUnit.unit)
          (0 : Fin (p+1)) = binaryMarkerLocalEquiv z := hh.trans hg
      exact hh'
    · intro i j u
      obtain ⟨g,hg⟩ := h i (oldIndex m p i j) u
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      refine ⟨⟨a.2,Subgroup.mem_map.mpr ⟨a,ha,rfl⟩⟩,?_⟩
      change a.2 i j = u
      rw [← binaryProductEquiv_old Ω m U p a i j]
      have hh := congrArg (fun x => x i (oldIndex m p i j)) he
      exact hh.trans hg
  · rintro ⟨hfirst,htail⟩ i j u
    have htail' (i : PUnit.{1} ⊕ α) (j : Fin (BaseMultiplicity m p i))
        (u : BaseAction Ω U i) :
        ∃ a : H, (binaryProductEquiv Ω m U p a.1) i (oldIndex m p i j) = u := by
      obtain ⟨g,hg⟩ := htail i j u
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      refine ⟨⟨a,ha⟩,?_⟩
      rw [binaryProductEquiv_old]
      change a.2 = g.1 at he
      rw [he]
      exact hg
    cases i with
    | inl i =>
      cases i
      refine Fin.cases ?_ (fun k => ?_) j
      · have hz : binaryMarkerLocalEquiv.symm u ∈
            H.map (MonoidHom.fst RepeatedMarkerMergedProfile.Sign
              (BaseOriginal Ω m U p)) := by
          rw [hfirst]
          trivial
        obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hz
        refine ⟨⟨binaryProductEquiv Ω m U p a,
          Subgroup.mem_map.mpr ⟨a,ha,rfl⟩⟩,?_⟩
        change binaryMarkerLocalEquiv a.1 = u
        change a.1 = binaryMarkerLocalEquiv.symm u at he
        rw [he,binaryMarkerLocalEquiv.apply_symm_apply]
      · obtain ⟨a,ha⟩ := htail' (.inl PUnit.unit) k u
        exact ⟨⟨binaryProductEquiv Ω m U p a.1,
          Subgroup.mem_map.mpr ⟨a.1,a.2,rfl⟩⟩,ha⟩
    | inr a =>
      obtain ⟨b,hb⟩ := htail' (.inr a) j u
      exact ⟨⟨binaryProductEquiv Ω m U p b.1,
        Subgroup.mem_map.mpr ⟨b.1,b.2,rfl⟩⟩,hb⟩

private def mappedFamilyEquiv {G D : Type*} [Group G] [Group D]
    (e : G ≃* D) (P : Subgroup G → Prop) (Q : Subgroup D → Prop)
    (h : ∀ H, P H ↔ Q (H.map e.toMonoidHom)) :
    {H : Subgroup G // P H} ≃ {J : Subgroup D // Q J} where
  toFun H := ⟨H.1.map e.toMonoidHom,(h H.1).mp H.2⟩
  invFun J := ⟨J.1.comap e.toMonoidHom,by
    apply (h _).mpr
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact J.2⟩
  left_inv H := Subtype.ext
    (Subgroup.comap_map_eq_self_of_injective e.injective H.1)
  right_inv J := Subtype.ext
    (Subgroup.map_comap_eq_self_of_surjective e.surjective J.1)

private theorem sign_isPGroup : IsPGroup 2 RepeatedMarkerMergedProfile.Sign := by
  intro x
  refine ⟨1, ?_⟩
  simpa only [pow_one] using binary_mul_pow_two x

private theorem baseAction_isPGroup (hU : ∀ a, IsPGroup 2 (U a)) :
    ∀ i, IsPGroup 2 (BaseAction Ω U i) := by
  intro i
  cases i with
  | inl _ => exact (sign_isPGroup.of_equiv binaryMarkerLocalEquiv)
  | inr a => exact hU a

/-- Exact arbitrary-exterior version of the one-marker contraction used in
the critical family. -/
def modelEquiv (hU : ∀ a, IsPGroup 2 (U a)) :
    OddModel Ω m U p ≃ BinaryModel Ω m U p :=
  (orbitProfileProductFullEquiv (OddMultiplicity m p) (OddAction Ω U)).symm |>.trans
    ((mappedFamilyEquiv (oddProductEquiv Ω m U p)
      (OrbitProfileProductFull (OddMultiplicity m p) (OddAction Ω U))
      (MarkerFull Ω m U p) (oddProduct_full_iff Ω m U p)).trans
    ((oddMarkerBinaryContractionEquiv
      (orbitProfileProduct_isPGroup (BaseMultiplicity m p) (BaseAction Ω U)
        (baseAction_isPGroup Ω U hU))
      (OrbitProfileProductFull (BaseMultiplicity m p) (BaseAction Ω U))).trans
    ((mappedFamilyEquiv (binaryProductEquiv Ω m U p)
      (MarkerFull Ω m U p)
      (OrbitProfileProductFull (RepeatedMarkerMergedProfile.multiplicity m (p+1))
        (BaseAction Ω U))
      (fun H => (binaryProduct_full_iff Ω m U p H).symm)).trans
      (orbitProfileProductFullEquiv
        (RepeatedMarkerMergedProfile.multiplicity m (p+1)) (BaseAction Ω U)))))

theorem model_card (hU : ∀ a, IsPGroup 2 (U a)) :
    Nat.card (OddModel Ω m U p) = Nat.card (BinaryModel Ω m U p) :=
  Nat.card_congr (modelEquiv Ω m U p hU)

end SymmetricSubgroupAsymptotics.OddMarkerPairModelEquiv

end
