import SymmetricSubgroupAsymptotics.BinaryS16LocalActionAlignment

/-!
# Common-source transport for the direct S16 decoder

Once two direct S16 keys have matched their literal source orbits, the two
canonical source products differ only by reindexing the occurrences and by
conjugating each local action through the exact matched-orbit chart.  This
file packages that change of source alphabet as one multiplicative
equivalence.

The final theorem is deliberately independent of the carrier routes.  It
says that equality of the complete correlated flat sources after this
transport is equivalent to equality of the original labelled permutation
subgroups.  Thus the semantic decoder may concentrate entirely on proving
that the physical target retains the transported flat source; no second
orbit or chart reconstruction argument is needed there.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16CommonSourceTransport

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierRoutedProfileAxisClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16JointOrbitData
open BinaryS16LocalActionAlignment
open BinaryS16SourceOrbitReindex

/-! ## A general map/comap comparison -/

/-- If two faithful target actions commute with equivalences of their source
and target groups, transporting the two complete comap sources is equivalent
to transporting the two target subgroups.  The range hypotheses are needed
only in the reverse direction: they say that the target subgroup really is
the image of its complete source. -/
theorem map_comap_equiv_iff
    {A B P Q : Type*} [Group A] [Group B] [Group P] [Group Q]
    (e : A ≃* B) (f : P ≃* Q) (a : A →* P) (b : B →* Q)
    (hcomm : f.toMonoidHom.comp a = b.comp e.toMonoidHom)
    (hb : Function.Injective b)
    (M : Subgroup P) (N : Subgroup Q)
    (hM : M ≤ a.range) (hN : N ≤ b.range) :
    (M.comap a).map e.toMonoidHom = N.comap b ↔
      M.map f.toMonoidHom = N := by
  constructor
  · intro hs
    calc
      M.map f.toMonoidHom =
          ((M.comap a).map a).map f.toMonoidHom := by
        rw [Subgroup.map_comap_eq_self hM]
      _ = (M.comap a).map (f.toMonoidHom.comp a) :=
        Subgroup.map_map _ _ _
      _ = (M.comap a).map (b.comp e.toMonoidHom) := by rw [hcomm]
      _ = ((M.comap a).map e.toMonoidHom).map b :=
        (Subgroup.map_map _ _ _).symm
      _ = (N.comap b).map b := congrArg (fun L : Subgroup B ↦ L.map b) hs
      _ = N := Subgroup.map_comap_eq_self hN
  · intro hMN
    apply Subgroup.map_injective (f := b) hb
    calc
      ((M.comap a).map e.toMonoidHom).map b =
          M.map f.toMonoidHom := by
        rw [Subgroup.map_map, ← hcomm, ← Subgroup.map_map,
          Subgroup.map_comap_eq_self hM]
      _ = N := hMN
      _ = (N.comap b).map b := (Subgroup.map_comap_eq_self hN).symm

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- The local action group at one literal occurrence. -/
abbrev LocalAction (H : Actual C) (q : Occurrence C H) :=
  action (subgroup C H) (residualSector C H) q.1

/-- The canonical flat product group before any carrier route is applied. -/
abbrev FlatGroup (H : Actual C) := ∀ q : Occurrence C H, LocalAction C H q

/-- The complete simultaneous profile point set belonging to one actual
subgroup. -/
abbrev ProfilePoints (H : Actual C) :=
  OrbitProfilePoints
    (Points (subgroup C H) (residualSector C H))
    (data (subgroup C H) (residualSector C H)).multiplicity

/-- Conjugate one matched local action through the exact equivalence which
preserves its original ambient labels. -/
def localActionEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q))
    (q : Occurrence C H) :
    LocalAction C H q ≃*
      LocalAction C K (occurrenceEquiv C hblocks htarget q) :=
  ((LocalAction C H q).equivMapOfInjective
      (occurrenceLocalPointEquiv C hblocks htarget q).permCongrHom.toMonoidHom
      (occurrenceLocalPointEquiv C hblocks htarget q).permCongrHom.injective).trans
    (MulEquiv.subgroupCongr (hlocal q))

/-- Reindex the product and conjugate every local action in one operation. -/
def flatGroupEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q)) :
    FlatGroup C H ≃* FlatGroup C K where
  toEquiv := (occurrenceEquiv C hblocks htarget).piCongr
    (fun q ↦ (localActionEquiv C hblocks htarget hlocal q).toEquiv)
  map_mul' := by
    intro x y
    apply funext
    intro q'
    obtain ⟨q,rfl⟩ := (occurrenceEquiv C hblocks htarget).surjective q'
    let E : FlatGroup C H ≃ FlatGroup C K :=
      (occurrenceEquiv C hblocks htarget).piCongr
      (fun q ↦ (localActionEquiv C hblocks htarget hlocal q).toEquiv)
    have happ (z : FlatGroup C H) :
        E z (occurrenceEquiv C hblocks htarget q) =
          localActionEquiv C hblocks htarget hlocal q (z q) := by
      exact Equiv.piCongr_apply_apply _ _ _ _
    change E (x * y) (occurrenceEquiv C hblocks htarget q) =
      (E x * E y) (occurrenceEquiv C hblocks htarget q)
    rw [happ]
    change localActionEquiv C hblocks htarget hlocal q (x q * y q) =
      E x (occurrenceEquiv C hblocks htarget q) *
        E y (occurrenceEquiv C hblocks htarget q)
    rw [happ, happ]
    exact map_mul (localActionEquiv C hblocks htarget hlocal q) (x q) (y q)

@[simp] theorem flatGroupEquiv_apply
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q))
    (x : FlatGroup C H) (q : Occurrence C H) :
    flatGroupEquiv C hblocks htarget hlocal x
        (occurrenceEquiv C hblocks htarget q) =
      localActionEquiv C hblocks htarget hlocal q (x q) :=
  Equiv.piCongr_apply_apply _ _ _ _

@[simp] theorem localActionEquiv_apply_point
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q))
    (q : Occurrence C H) (u : LocalAction C H q)
    (x : Points (subgroup C H) (residualSector C H) q.1) :
    ((localActionEquiv C hblocks htarget hlocal q u :
        LocalAction C K (occurrenceEquiv C hblocks htarget q)) :
          Equiv.Perm (Points (subgroup C K) (residualSector C K)
            (occurrenceEquiv C hblocks htarget q).1))
        (occurrenceLocalPointEquiv C hblocks htarget q x) =
      occurrenceLocalPointEquiv C hblocks htarget q
        ((u : Equiv.Perm
          (Points (subgroup C H) (residualSector C H) q.1)) x) := by
  change (occurrenceLocalPointEquiv C hblocks htarget q).permCongr
      (u : Equiv.Perm
        (Points (subgroup C H) (residualSector C H) q.1))
      (occurrenceLocalPointEquiv C hblocks htarget q x) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

@[simp] theorem profilePointEquiv_apply
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H)
    (x : Points (subgroup C H) (residualSector C H) q.1) :
    profilePointEquiv C hblocks htarget ⟨q.1,q.2,x⟩ =
      ⟨(occurrenceEquiv C hblocks htarget q).1,
        (occurrenceEquiv C hblocks htarget q).2,
        occurrenceLocalPointEquiv C hblocks htarget q x⟩ := by
  rfl

/-! ## The two flat product actions commute -/

/-- Act on the complete profile directly from the flattened occurrence
product. -/
def flatAction (H : Actual C) :
    FlatGroup C H →* Equiv.Perm (ProfilePoints C H) :=
  (orbitProfileProductAction
      (data (subgroup C H) (residualSector C H)).multiplicity
      (action (subgroup C H) (residualSector C H))).comp
    (flatten
      (Points (subgroup C H) (residualSector C H))
      (action (subgroup C H) (residualSector C H))
      (data (subgroup C H) (residualSector C H)).multiplicity).symm.toMonoidHom

@[simp] theorem flatAction_apply
    (H : Actual C) (x : FlatGroup C H)
    (z : ProfilePoints C H) :
    flatAction C H x z =
      ⟨z.1,z.2.1,
        ((x ⟨z.1,z.2.1⟩ : LocalAction C H ⟨z.1,z.2.1⟩) :
          Equiv.Perm (Points (subgroup C H) (residualSector C H) z.1))
          z.2.2⟩ := by
  rfl

theorem flatAction_injective (H : Actual C) :
    Function.Injective (flatAction C H) :=
  (orbitProfileProductAction_injective
      (data (subgroup C H) (residualSector C H)).multiplicity
      (action (subgroup C H) (residualSector C H))).comp
    (flatten
      (Points (subgroup C H) (residualSector C H))
      (action (subgroup C H) (residualSector C H))
      (data (subgroup C H) (residualSector C H)).multiplicity).symm.injective

/-- The point reindexing and the flat product reindexing conjugate the two
independent product actions exactly. -/
theorem flatAction_intertwine
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q))
    (x : FlatGroup C H) :
    (profilePointEquiv C hblocks htarget).permCongr
        (flatAction C H x) =
      flatAction C K (flatGroupEquiv C hblocks htarget hlocal x) := by
  apply Equiv.ext
  intro z'
  obtain ⟨z,rfl⟩ := (profilePointEquiv C hblocks htarget).surjective z'
  rcases z with ⟨o,j,p⟩
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
    flatAction_apply]
  rw [profilePointEquiv_apply C hblocks htarget ⟨o,j⟩
      (((x ⟨o,j⟩ : LocalAction C H ⟨o,j⟩) :
        Equiv.Perm (Points (subgroup C H) (residualSector C H) o)) p),
    profilePointEquiv_apply C hblocks htarget ⟨o,j⟩ p]
  rw [flatGroupEquiv_apply C hblocks htarget hlocal x ⟨o,j⟩]
  rw [localActionEquiv_apply_point C hblocks htarget hlocal ⟨o,j⟩
    (x ⟨o,j⟩) p]

theorem flatAction_commutes
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q)) :
    (profilePointEquiv C hblocks htarget).permCongrHom.toMonoidHom.comp
        (flatAction C H) =
      (flatAction C K).comp
        (flatGroupEquiv C hblocks htarget hlocal).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  exact flatAction_intertwine C hblocks htarget hlocal x

/-! ## Complete-source reconstruction -/

/-- The canonical flat source is exactly the comap of the canonical model
through the faithful flat product action. -/
theorem flatSource_eq_model_comap (H : Actual C) :
    CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H)) =
      (CanonicalOrbitWord.model
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).comap
          (flatAction C H) := by
  unfold CanonicalOrbitWord.flatSource CanonicalOrbitWord.profileSource
  rw [Subgroup.map_equiv_eq_comap_symm']
  rfl

/-- Fullness says that the canonical model lies in the range of the flat
product action, including all cross-orbit correlations. -/
theorem model_le_flatAction_range (H : Actual C) :
    CanonicalOrbitWord.model
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H)) ≤
      (flatAction C H).range := by
  intro g hg
  have hg' := orbitProfileFull_le_product_range
    (CanonicalOrbitWord.model_full
      (Points (subgroup C H) (residualSector C H))
      (action (subgroup C H) (residualSector C H))
      (subgroup C H)
      (data (subgroup C H) (residualSector C H))) hg
  obtain ⟨d,hd⟩ := hg'
  refine ⟨(flatten
    (Points (subgroup C H) (residualSector C H))
    (action (subgroup C H) (residualSector C H))
    (data (subgroup C H) (residualSector C H)).multiplicity) d, ?_⟩
  change orbitProfileProductAction
      (data (subgroup C H) (residualSector C H)).multiplicity
      (action (subgroup C H) (residualSector C H))
      ((flatten
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (data (subgroup C H) (residualSector C H)).multiplicity).symm
          ((flatten
            (Points (subgroup C H) (residualSector C H))
            (action (subgroup C H) (residualSector C H))
            (data (subgroup C H) (residualSector C H)).multiplicity) d)) = g
  rw [MulEquiv.symm_apply_apply]
  exact hd

/-- The exact source-orbit reindexing makes the two simultaneous charts into
the ambient labelled set commute. -/
theorem profilePointEquiv_trans_chart
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    (profilePointEquiv C hblocks htarget).trans
        (data (subgroup C K) (residualSector C K)).chart =
      (data (subgroup C H) (residualSector C H)).chart := by
  apply Equiv.ext
  intro z
  exact profilePointEquiv_chart C hblocks htarget z

/-- Transporting the two canonical models through the common profile chart
is equivalent to equality of the original labelled subgroups. -/
theorem model_map_profilePointEquiv_iff
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    (CanonicalOrbitWord.model
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map
          (profilePointEquiv C hblocks htarget).permCongrHom.toMonoidHom =
      CanonicalOrbitWord.model
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K)) ↔
      subgroup C H = subgroup C K := by
  let eH := (data (subgroup C H) (residualSector C H)).chart
  let eK := (data (subgroup C K) (residualSector C K)).chart
  let p := profilePointEquiv C hblocks htarget
  have hp : p.trans eK = eH :=
    profilePointEquiv_trans_chart C hblocks htarget
  have hp' : eH.symm.trans p = eK.symm := by
    apply Equiv.ext
    intro x
    apply eK.injective
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrArg (fun f : ProfilePoints C H ≃ Fin (2 * N) ↦ f (eH.symm x)) hp
  constructor
  · intro hmodel
    calc
      subgroup C H = relabelSubgroup eH
          (CanonicalOrbitWord.model
            (Points (subgroup C H) (residualSector C H))
            (action (subgroup C H) (residualSector C H))
            (subgroup C H)
            (data (subgroup C H) (residualSector C H))) :=
        (relabelSubgroup_symm eH.symm (subgroup C H)).symm
      _ = relabelSubgroup eK
          (relabelSubgroup p
            (CanonicalOrbitWord.model
              (Points (subgroup C H) (residualSector C H))
              (action (subgroup C H) (residualSector C H))
              (subgroup C H)
              (data (subgroup C H) (residualSector C H)))) := by
        rw [relabelSubgroup_trans, hp]
      _ = relabelSubgroup eK
          (CanonicalOrbitWord.model
            (Points (subgroup C K) (residualSector C K))
            (action (subgroup C K) (residualSector C K))
            (subgroup C K)
            (data (subgroup C K) (residualSector C K))) := by
        exact congrArg (relabelSubgroup eK) hmodel
      _ = subgroup C K :=
        relabelSubgroup_symm eK.symm (subgroup C K)
  · intro hsubgroup
    change relabelSubgroup p
        (relabelSubgroup eH.symm (subgroup C H)) =
      relabelSubgroup eK.symm (subgroup C K)
    rw [relabelSubgroup_trans, hp', hsubgroup]

/-- **Common-source reconstruction.**  After the exact source-orbit and
local-action reindexing, equality of the complete correlated carrier sources
is equivalent to equality of the original labelled subgroups.  This is the
route-independent terminal theorem needed by the direct physical decoder. -/
theorem flatSource_transport_iff_subgroup_eq
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (hlocal : ∀ q : Occurrence C H,
      relabelSubgroup (occurrenceLocalPointEquiv C hblocks htarget q)
          (LocalAction C H q) =
        LocalAction C K (occurrenceEquiv C hblocks htarget q)) :
    (CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map
          (flatGroupEquiv C hblocks htarget hlocal).toMonoidHom =
      CanonicalOrbitWord.flatSource
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K)) ↔
      subgroup C H = subgroup C K := by
  rw [flatSource_eq_model_comap C H, flatSource_eq_model_comap C K]
  exact (map_comap_equiv_iff
    (flatGroupEquiv C hblocks htarget hlocal)
    (profilePointEquiv C hblocks htarget).permCongrHom
    (flatAction C H) (flatAction C K)
    (flatAction_commutes C hblocks htarget hlocal)
    (flatAction_injective C K)
    (CanonicalOrbitWord.model
      (Points (subgroup C H) (residualSector C H))
      (action (subgroup C H) (residualSector C H))
      (subgroup C H)
      (data (subgroup C H) (residualSector C H)))
    (CanonicalOrbitWord.model
      (Points (subgroup C K) (residualSector C K))
      (action (subgroup C K) (residualSector C K))
      (subgroup C K)
      (data (subgroup C K) (residualSector C K)))
    (model_le_flatAction_range C H)
    (model_le_flatAction_range C K)).trans
      (model_map_profilePointEquiv_iff C hblocks htarget)

/-- The canonical product equivalence for a matched physical key.  The local
conjugacy premise of `flatGroupEquiv` is discharged by the complete
recorded/unrecorded orbit-image alignment theorem. -/
def canonicalFlatGroupEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    FlatGroup C H ≃* FlatGroup C K :=
  flatGroupEquiv C hblocks htarget
    (occurrenceLocalPointEquiv_action C hblocks htarget)

/-- Fully discharged common-source reconstruction for the direct S16 key.
After the retained table and target subgroup have matched, transporting the
complete correlated flat source through the canonical occurrence/local-action
equivalence recovers the original subgroup with fibre one. -/
theorem canonicalFlatSource_transport_iff_subgroup_eq
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    (CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map
          (canonicalFlatGroupEquiv C hblocks htarget).toMonoidHom =
      CanonicalOrbitWord.flatSource
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K)) ↔
      subgroup C H = subgroup C K :=
  flatSource_transport_iff_subgroup_eq C hblocks htarget
    (occurrenceLocalPointEquiv_action C hblocks htarget)

end SymmetricSubgroupAsymptotics.BinaryS16CommonSourceTransport

end
