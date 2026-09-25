import SymmetricSubgroupAsymptotics.OddMarker
import SymmetricSubgroupAsymptotics.CriticalProductTransport
import SymmetricSubgroupAsymptotics.OddProfileActions

/-! Exact singleton and S3 critical-profile model fibres. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Add the binary quotient coordinate of one natural S3 marker. -/
def CriticalProfile.addC2 (p : CriticalProfile) : CriticalProfile :=
  { p with c2 := p.c2 + 1 }

@[simp] theorem CriticalProfile.addC2_rank (p : CriticalProfile) :
    p.addC2.rank = p.rank + 1 := by
  simp [CriticalProfile.addC2, CriticalProfile.rank]
  omega

abbrev CriticalOriginalProduct (p : CriticalProfile) :=
  OrbitProfileProductGroup p.multiplicity criticalActionSubgroup

/-- The actual original-action product has exponent dividing four. -/
theorem criticalOriginalProduct_pow_four (p : CriticalProfile)
    (g : CriticalOriginalProduct p) : g ^ 4 = 1 := by
  apply (criticalProfileProductEquiv p).injective
  rw [map_pow, map_one]
  exact criticalProduct_pow_four _ _ _

/-- The scalar marker quotient is the original regular two-point action. -/
def binaryMarkerLocalEquiv : Multiplicative (ZMod 2) ≃* criticalActionSubgroup .c2 where
  toFun z := criticalLocalEquiv .c2 (Multiplicative.ofAdd (fun _ => z.toAdd))
  invFun u := Multiplicative.ofAdd (((criticalLocalEquiv .c2).symm u).toAdd 0)
  left_inv z := by simp
  right_inv u := by
    apply (criticalLocalEquiv .c2).symm.injective
    simp only [MulEquiv.symm_apply_apply]
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg (((criticalLocalEquiv .c2).symm u).toAdd) (Subsingleton.elim 0 i)
  map_mul' z w := by
    rw [← map_mul]
    rfl

/-- Install the marker quotient as the first original C2 occurrence. -/
def criticalAddC2ProductEquiv (p : CriticalProfile) :
    Multiplicative (ZMod 2) × CriticalOriginalProduct p ≃* CriticalOriginalProduct p.addC2 where
  toFun g i := match i with
    | .c2 => Fin.cons (binaryMarkerLocalEquiv g.1) (g.2 .c2)
    | .v4 => g.2 .v4
    | .d8 => g.2 .d8
    | .e8 => g.2 .e8
  invFun g := (binaryMarkerLocalEquiv.symm (g .c2 (0 : Fin (p.c2 + 1))), fun i => match i with
    | .c2 => fun j => g .c2 j.succ
    | .v4 => g .v4
    | .d8 => g .d8
    | .e8 => g .e8)
  left_inv g := by
    apply Prod.ext
    · exact binaryMarkerLocalEquiv.symm_apply_apply _
    · funext i j
      cases i <;> rfl
  right_inv g := by
    funext i j
    cases i with
    | c2 =>
      refine Fin.cases ?_ (fun k => ?_) j
      · exact binaryMarkerLocalEquiv.apply_symm_apply _
      · rfl
    | v4 => rfl
    | d8 => rfl
    | e8 => rfl
  map_mul' g h := by
    funext i j
    cases i with
    | c2 =>
      refine Fin.cases ?_ (fun k => ?_) j
      · exact binaryMarkerLocalEquiv.map_mul _ _
      · rfl
    | v4 => rfl
    | d8 => rfl
    | e8 => rfl

/-- Fullness keeps the marker coordinate and every original exterior block. -/
def MarkerProductFull {G : Type*} [Group G] (p : CriticalProfile)
    (H : Subgroup (G × CriticalOriginalProduct p)) : Prop :=
  H.map (MonoidHom.fst G _) = ⊤ ∧
    OrbitProfileProductFull p.multiplicity criticalActionSubgroup
      (H.map (MonoidHom.snd G _))

/-- An actual S3-full product fibre, before any contraction. -/
abbrev OddS3ProductModels (p : CriticalProfile) :=
  {H : Subgroup (OddMarkerGroup × CriticalOriginalProduct p) // MarkerProductFull p H}

/-- An actual full binary marker product fibre. -/
abbrev OddBinaryProductModels (p : CriticalProfile) :=
  {H : Subgroup (Multiplicative (ZMod 2) × CriticalOriginalProduct p) // MarkerProductFull p H}

/-- S3 contraction retains all original block fullness predicates. -/
def oddS3ProductContractionEquiv (p : CriticalProfile) :
    OddS3ProductModels p ≃ OddBinaryProductModels p :=
  oddMarkerContractionEquiv (criticalOriginalProduct_pow_four p)
    (OrbitProfileProductFull p.multiplicity criticalActionSubgroup)

/-- Original exterior occurrences are retained literally after the new head. -/
def criticalAddC2TailIndex (p : CriticalProfile) (i : CriticalActionKind) :
    Fin (p.multiplicity i) → Fin (p.addC2.multiplicity i) := by
  cases i with
  | c2 => exact Fin.succ
  | v4 => exact id
  | d8 => exact id
  | e8 => exact id

@[simp] theorem criticalAddC2ProductEquiv_tail (p : CriticalProfile)
    (g : Multiplicative (ZMod 2) × CriticalOriginalProduct p)
    (i : CriticalActionKind) (j : Fin (p.multiplicity i)) :
    criticalAddC2ProductEquiv p g i (criticalAddC2TailIndex p i j) = g.2 i j := by
  cases i <;> rfl

/-- The extra C2 condition is precisely fullness of the contracted marker;
all other conditions remain fullness on each original exterior block. -/
theorem criticalAddC2Product_full_iff (p : CriticalProfile)
    (H : Subgroup (Multiplicative (ZMod 2) × CriticalOriginalProduct p)) :
    OrbitProfileProductFull p.addC2.multiplicity criticalActionSubgroup
      (H.map (criticalAddC2ProductEquiv p).toMonoidHom) ↔ MarkerProductFull p H := by
  constructor
  · intro h
    constructor
    · apply top_unique
      intro z _
      obtain ⟨g,hg⟩ := h .c2 (0 : Fin (p.c2 + 1)) (binaryMarkerLocalEquiv z)
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      change criticalAddC2ProductEquiv p a = g.1 at he
      refine Subgroup.mem_map.mpr ⟨a,ha,?_⟩
      apply binaryMarkerLocalEquiv.injective
      change binaryMarkerLocalEquiv a.1 = binaryMarkerLocalEquiv z
      have hhead : (criticalAddC2ProductEquiv p a) .c2 (0 : Fin (p.c2 + 1)) = binaryMarkerLocalEquiv z := by
        rw [he]; exact hg
      exact hhead
    · intro i j u
      obtain ⟨g,hg⟩ := h i (criticalAddC2TailIndex p i j) u
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      change criticalAddC2ProductEquiv p a = g.1 at he
      refine ⟨⟨a.2,Subgroup.mem_map.mpr ⟨a,ha,rfl⟩⟩,?_⟩
      change a.2 i j = u
      rw [← criticalAddC2ProductEquiv_tail p a i j, he]
      exact hg
  · rintro ⟨hfirst,htail⟩
    have htail' (i : CriticalActionKind) (j : Fin (p.multiplicity i)) (u : criticalActionSubgroup i) :
        ∃ a : H, (criticalAddC2ProductEquiv p a.1) i (criticalAddC2TailIndex p i j) = u := by
      obtain ⟨g,hg⟩ := htail i j u
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      refine ⟨⟨a,ha⟩,?_⟩
      rw [criticalAddC2ProductEquiv_tail]
      change a.2 = g.1 at he
      rw [he]
      exact hg
    intro i j u
    have hlift (a : H) (h : (criticalAddC2ProductEquiv p a.1) i j = u) :
        ∃ g : H.map (criticalAddC2ProductEquiv p).toMonoidHom, g.1 i j = u :=
      ⟨⟨criticalAddC2ProductEquiv p a.1,Subgroup.mem_map.mpr ⟨a.1,a.2,rfl⟩⟩,h⟩
    cases i with
    | c2 =>
      refine Fin.cases ?_ (fun k => ?_) j
      · have hz : binaryMarkerLocalEquiv.symm u ∈
            H.map (MonoidHom.fst (Multiplicative (ZMod 2)) (CriticalOriginalProduct p)) := by
          rw [hfirst]; trivial
        obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hz
        refine ⟨⟨criticalAddC2ProductEquiv p a,Subgroup.mem_map.mpr ⟨a,ha,rfl⟩⟩,?_⟩
        change binaryMarkerLocalEquiv a.1 = u
        change a.1 = binaryMarkerLocalEquiv.symm u at he
        rw [he, binaryMarkerLocalEquiv.apply_symm_apply]
      · obtain ⟨a,ha⟩ := htail' .c2 k u
        exact ⟨⟨criticalAddC2ProductEquiv p a.1,Subgroup.mem_map.mpr ⟨a.1,a.2,rfl⟩⟩,ha⟩
    | v4 => obtain ⟨a,ha⟩ := htail' .v4 j u; exact hlift a ha
    | d8 => obtain ⟨a,ha⟩ := htail' .d8 j u; exact hlift a ha
    | e8 => obtain ⟨a,ha⟩ := htail' .e8 j u; exact hlift a ha

/-- An exact subgroup equivalence, not a substitution of model counts. -/
def oddBinaryProductModelsEquiv (p : CriticalProfile) :
    OddBinaryProductModels p ≃
      {H : Subgroup (CriticalOriginalProduct p.addC2) //
        OrbitProfileProductFull p.addC2.multiplicity criticalActionSubgroup H} where
  toFun H := ⟨H.1.map (criticalAddC2ProductEquiv p).toMonoidHom,
    (criticalAddC2Product_full_iff p H.1).mpr H.2⟩
  invFun H := ⟨H.1.comap (criticalAddC2ProductEquiv p).toMonoidHom, by
    apply (criticalAddC2Product_full_iff p _).mp
    rw [Subgroup.map_comap_eq_self_of_surjective (criticalAddC2ProductEquiv p).surjective]
    exact H.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self_of_injective
    (criticalAddC2ProductEquiv p).injective H.1)
  right_inv H := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective
    (criticalAddC2ProductEquiv p).surjective H.1)

/-- The full natural S3 fibre equals the critical model fibre with one
additional C2 quotient coordinate. Its physical orbit weight stays 1/6. -/
def oddS3ProductModelsEquivCritical (p : CriticalProfile) :
    OddS3ProductModels p ≃ CriticalModelSubgroups p.addC2 :=
  (oddS3ProductContractionEquiv p).trans
    ((oddBinaryProductModelsEquiv p).trans (criticalModelSubgroupsEquivProduct p.addC2).symm)

theorem oddS3ProductModels_card (p : CriticalProfile) :
    Nat.card (OddS3ProductModels p) = Nat.card (CriticalModelSubgroups p.addC2) :=
  Nat.card_congr (oddS3ProductModelsEquivCritical p)

private def oddFullSubgroupEquiv {G D : Type*} [Group G] [Group D]
    (e : G ≃* D) (P : Subgroup G → Prop) (Q : Subgroup D → Prop)
    (h : ∀ H, P H ↔ Q (H.map e.toMonoidHom)) :
    {H : Subgroup G // P H} ≃ {J : Subgroup D // Q J} where
  toFun H := ⟨H.1.map e.toMonoidHom,(h H.1).mp H.2⟩
  invFun J := ⟨J.1.comap e.toMonoidHom,by
    apply (h _).mpr
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact J.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self_of_injective e.injective H.1)
  right_inv J := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective e.surjective J.1)

/-- Deleting the unique fixed point removes only a trivial factor. -/
def oddSingletonProductEquiv (p : CriticalProfile) :
    OrbitProfileProductGroup (oddCriticalMultiplicity false p) oddCriticalActionSubgroup ≃*
      CriticalOriginalProduct p where
  toFun g i := g (.binary i)
  invFun g i := match i with
    | .fixed => fun _ => 1
    | .marker => fun j => Fin.elim0 j
    | .binary i => g i
  left_inv g := by
    funext i j
    cases i with
    | fixed =>
      apply Subtype.ext
      apply Equiv.ext
      intro x
      exact @Subsingleton.elim (Fin 1) inferInstance _ _
    | marker => exact Fin.elim0 j
    | binary i => rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem oddSingletonProduct_full_iff (p : CriticalProfile)
    (H : Subgroup (OrbitProfileProductGroup (oddCriticalMultiplicity false p)
      oddCriticalActionSubgroup)) :
    OrbitProfileProductFull (oddCriticalMultiplicity false p) oddCriticalActionSubgroup H ↔
      OrbitProfileProductFull p.multiplicity criticalActionSubgroup
        (H.map (oddSingletonProductEquiv p).toMonoidHom) := by
  constructor
  · intro h i j u
    obtain ⟨g,hg⟩ := h (.binary i) j u
    exact ⟨⟨oddSingletonProductEquiv p g.1,Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩⟩,hg⟩
  · intro h i j u
    cases i with
    | fixed =>
      refine ⟨1,?_⟩
      apply Subtype.ext
      apply Equiv.ext
      intro x
      exact @Subsingleton.elim (Fin 1) inferInstance _ _
    | marker => exact Fin.elim0 j
    | binary i =>
      obtain ⟨g,hg⟩ := h i j u
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp g.2
      refine ⟨⟨a,ha⟩,?_⟩
      change oddSingletonProductEquiv p a = g.1 at he
      change (oddSingletonProductEquiv p a) i j = u
      rw [he]
      exact hg

/-- Literal singleton model fibres are exactly the exterior critical fibres. -/
def oddSingletonModelEquiv (p : CriticalProfile) :
    OddCriticalModelSubgroups false p ≃ CriticalModelSubgroups p :=
  (orbitProfileProductFullEquiv (oddCriticalMultiplicity false p) oddCriticalActionSubgroup).symm.trans
    ((oddFullSubgroupEquiv (oddSingletonProductEquiv p)
      (OrbitProfileProductFull (oddCriticalMultiplicity false p) oddCriticalActionSubgroup)
      (OrbitProfileProductFull p.multiplicity criticalActionSubgroup)
      (oddSingletonProduct_full_iff p)).trans (criticalModelSubgroupsEquivProduct p).symm)

/-- Splitting the original natural S3 occurrence is an actual group equivalence. -/
def oddS3OriginalProductEquiv (p : CriticalProfile) :
    OrbitProfileProductGroup (oddCriticalMultiplicity true p) oddCriticalActionSubgroup ≃*
      OddMarkerGroup × CriticalOriginalProduct p where
  toFun g := ((g .marker (0 : Fin 1)).1, fun i => g (.binary i))
  invFun g i := match i with
    | .fixed => fun j => Fin.elim0 j
    | .marker => fun _ => ⟨g.1,Subgroup.mem_top _⟩
    | .binary i => g.2 i
  left_inv g := by
    funext i j
    cases i with
    | fixed => exact Fin.elim0 j
    | marker =>
      have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst j
      rfl
    | binary i => rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem oddS3OriginalProduct_full_iff (p : CriticalProfile)
    (H : Subgroup (OrbitProfileProductGroup (oddCriticalMultiplicity true p)
      oddCriticalActionSubgroup)) :
    OrbitProfileProductFull (oddCriticalMultiplicity true p) oddCriticalActionSubgroup H ↔
      MarkerProductFull p (H.map (oddS3OriginalProductEquiv p).toMonoidHom) := by
  constructor
  · intro h
    constructor
    · apply top_unique
      intro z _
      obtain ⟨g,hg⟩ := h .marker (0 : Fin 1) ⟨z,Subgroup.mem_top _⟩
      refine Subgroup.mem_map.mpr ⟨oddS3OriginalProductEquiv p g.1,
        Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩,?_⟩
      exact congrArg Subtype.val hg
    · intro i j u
      obtain ⟨g,hg⟩ := h (.binary i) j u
      exact ⟨⟨(oddS3OriginalProductEquiv p g.1).2,
        Subgroup.mem_map.mpr ⟨oddS3OriginalProductEquiv p g.1,
          Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩,rfl⟩⟩,hg⟩
  · rintro ⟨hfirst,htail⟩ i j u
    cases i with
    | fixed => exact Fin.elim0 j
    | marker =>
      have hu : u.1 ∈ (H.map (oddS3OriginalProductEquiv p).toMonoidHom).map
          (MonoidHom.fst OddMarkerGroup (CriticalOriginalProduct p)) := by
        rw [hfirst]; trivial
      obtain ⟨g,hg,hgu⟩ := Subgroup.mem_map.mp hu
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hg
      refine ⟨⟨a,ha⟩,?_⟩
      apply Subtype.ext
      have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst j
      change oddS3OriginalProductEquiv p a = g at he
      change g.1 = u.1 at hgu
      exact (congrArg Prod.fst he).trans hgu
    | binary i =>
      obtain ⟨g,hg⟩ := htail i j u
      obtain ⟨b,hb,hbg⟩ := Subgroup.mem_map.mp g.2
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp hb
      refine ⟨⟨a,ha⟩,?_⟩
      change oddS3OriginalProductEquiv p a = b at he
      change b.2 = g.1 at hbg
      have hat : (oddS3OriginalProductEquiv p a).2 = g.1 :=
        (congrArg Prod.snd he).trans hbg
      change (oddS3OriginalProductEquiv p a).2 i j = u
      rw [hat]
      exact hg

/-- All S3 marker model subgroups contract bijectively to critical models at
one greater binary rank, retaining every original exterior fullness condition. -/
def oddS3ModelEquiv (p : CriticalProfile) :
    OddCriticalModelSubgroups true p ≃ CriticalModelSubgroups p.addC2 :=
  (orbitProfileProductFullEquiv (oddCriticalMultiplicity true p) oddCriticalActionSubgroup).symm.trans
    ((oddFullSubgroupEquiv (oddS3OriginalProductEquiv p)
      (OrbitProfileProductFull (oddCriticalMultiplicity true p) oddCriticalActionSubgroup)
      (MarkerProductFull p) (oddS3OriginalProduct_full_iff p)).trans
      (oddS3ProductModelsEquivCritical p))

theorem oddSingletonModel_card (p : CriticalProfile) :
    Nat.card (OddCriticalModelSubgroups false p) = Nat.card (CriticalModelSubgroups p) :=
  Nat.card_congr (oddSingletonModelEquiv p)

theorem oddS3Model_card (p : CriticalProfile) :
    Nat.card (OddCriticalModelSubgroups true p) = Nat.card (CriticalModelSubgroups p.addC2) :=
  Nat.card_congr (oddS3ModelEquiv p)

theorem oddSingletonProfile_card (p : CriticalProfile) :
    (Nat.card (OddCriticalProfileSubgroups false p) : ℚ) =
      ((2 * p.rank + 1).factorial : ℚ) * p.weight * Nat.card (CriticalModelSubgroups p) := by
  simpa only [Bool.false_eq_true, ↓reduceIte, div_one, oddSingletonModel_card]
    using oddCriticalProfileSubgroups_card false p

theorem oddS3Profile_card (p : CriticalProfile) :
    (Nat.card (OddCriticalProfileSubgroups true p) : ℚ) =
      ((2 * p.rank + 3).factorial : ℚ) * (p.weight / 6) *
        Nat.card (CriticalModelSubgroups p.addC2) := by
  simpa only [↓reduceIte, oddS3Model_card] using oddCriticalProfileSubgroups_card true p

end SymmetricSubgroupAsymptotics
