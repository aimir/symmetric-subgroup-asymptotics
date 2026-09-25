import SymmetricSubgroupAsymptotics.TerminalFibreCount
import SymmetricSubgroupAsymptotics.TerminalGraphClassification

/-!
# Central binary extension comparison with the split extension

The comparison counts literal subgroups and keeps their exact exterior image.
The original extension need not split, and its exterior may be nonabelian.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {X Y K : Type*} [Group X] [Group Y]
  [AddCommGroup K] [Module (ZMod 2) K]
  (π : X →* Y) (e : Multiplicative K ≃* π.ker)

/-- Each nonempty original fixed-intersection fibre has an origin selected
once for that intersection, not separately for every subgroup. -/
def binaryCentralFibreOrigin (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [FiniteDimensional (ZMod 2) K]
    (W : {W : Submodule (ZMod 2) K // W.dualAnnihilator ≤ terminalSplittingAnnihilator π e}) :
    TerminalLiftFibre π e W.1 :=
  Classical.choice ((terminalLiftFibre_nonempty_iff π e hπ hc W.1).mpr W.2)

/-- The nonsplit full-image family injects into the actual split family.
The split target retains the entire quotient Y and the actual K/W character. -/
def binaryCentralFullSplitMap (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [FiniteDimensional (ZMod 2) K] :
    {H : Subgroup X // H.map π = ⊤} → TerminalFullImages (V := K) (T := Y) :=
  (terminalGraphAdditiveClassification (V := K) (T := Y)).symm ∘
    (Sigma.map Subtype.val (fun W => terminalLiftFibreHomEquiv π e hπ hc W.1
      (binaryCentralFibreOrigin π e hπ hc W))) ∘
    (terminalAllLiftFibreEquiv π e hπ hc).symm

theorem binaryCentralFullSplitMap_injective (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [FiniteDimensional (ZMod 2) K] :
    Function.Injective (binaryCentralFullSplitMap π e hπ hc) := by
  apply (terminalGraphAdditiveClassification (V := K) (T := Y)).symm.injective.comp
  apply Function.Injective.comp _ (terminalAllLiftFibreEquiv π e hπ hc).symm.injective
  exact Subtype.val_injective.sigma_map (fun W =>
    (terminalLiftFibreHomEquiv π e hπ hc W.1 (binaryCentralFibreOrigin π e hπ hc W)).injective)

include e in
theorem binaryCentralFull_card_le_split (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [Finite Y] [Finite K] :
    Nat.card {H : Subgroup X // H.map π = ⊤} ≤ Nat.card (TerminalFullImages (V := K) (T := Y)) :=
  Nat.card_le_card_of_injective _ (binaryCentralFullSplitMap_injective π e hπ hc)

/-- Restrict the original extension to the entire preimage of a literal
subgroup of its exterior, with no change to the kernel. -/
def binaryCentralRestrictedProjection (L : Subgroup Y) : L.comap π →* L where
  toFun x := ⟨π x.1,x.2⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' x y := Subtype.ext (map_mul π x.1 y.1)

theorem binaryCentralRestrictedProjection_surjective
    (hπ : Function.Surjective π) (L : Subgroup Y) :
    Function.Surjective (binaryCentralRestrictedProjection π L) := by
  intro y
  obtain ⟨x,hx⟩ := hπ y.1
  exact ⟨⟨x,by change π x ∈ L; rw [hx]; exact y.2⟩,Subtype.ext hx⟩

/-- The restricted extension retains exactly the original kernel chart. -/
def binaryCentralRestrictedKernel (L : Subgroup Y) :
    Multiplicative K ≃* (binaryCentralRestrictedProjection π L).ker where
  toFun k := ⟨⟨(e k).1,by
    change π (e k).1 ∈ L
    rw [(e k).2]
    exact L.one_mem⟩,Subtype.ext (e k).2⟩
  invFun x := e.symm ⟨x.1.1,congrArg Subtype.val x.2⟩
  left_inv k := by exact e.symm_apply_apply k
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : π.ker => k.1) (e.apply_symm_apply _)
  map_mul' k l := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : π.ker => k.1) (map_mul e k l)

theorem binaryCentralRestrictedKernel_central (hc : π.ker ≤ Subgroup.center X)
    (L : Subgroup Y) :
    (binaryCentralRestrictedProjection π L).ker ≤ Subgroup.center (L.comap π) := by
  intro k hk
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hc (congrArg Subtype.val hk)) x.1

/-- Original subgroups with image exactly L are the full-image subgroups
of the complete original preimage extension. -/
def binaryCentralImageFibreEquiv (L : Subgroup Y) :
    {H : Subgroup X // H.map π = L} ≃
      {H : Subgroup (L.comap π) // H.map (binaryCentralRestrictedProjection π L) = ⊤} where
  toFun H := ⟨H.1.comap (L.comap π).subtype,by
    apply top_unique
    intro y _
    have hy : y.1 ∈ H.1.map π := by rw [H.2]; exact y.2
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨⟨x,by change π x ∈ L; rw [he]; exact y.2⟩,
      hx,Subtype.ext he⟩⟩
  invFun H := ⟨H.1.map (L.comap π).subtype,by
    rw [Subgroup.map_map]
    have he : π.comp (L.comap π).subtype =
        L.subtype.comp (binaryCentralRestrictedProjection π L) := rfl
    rw [he,← Subgroup.map_map,H.2,← MonoidHom.range_eq_map,Subgroup.range_subtype]⟩
  left_inv H := by
    apply Subtype.ext
    apply Subgroup.map_comap_eq_self
    rw [Subgroup.range_subtype]
    intro x hx
    change π x ∈ L
    rw [← H.2]
    exact Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  right_inv H := Subtype.ext (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective H.1)


/-- The complete preimage of L in a split product is exactly K×L. -/
def binarySplitPreimageEquiv (L : Subgroup Y) :
    L.comap (MonoidHom.snd (Multiplicative K) Y) ≃* (Multiplicative K × L) where
  toFun x := (x.1.1,⟨x.1.2,x.2⟩)
  invFun x := ⟨(x.1,x.2.1),x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Full images over L in the split extension count the same literal
subgroups as the fixed-image fibre in K×Y. -/
def binarySplitImageFibreEquiv (L : Subgroup Y) :
    {H : Subgroup (Multiplicative K × Y) //
      H.map (MonoidHom.snd (Multiplicative K) Y) = L} ≃
      TerminalFullImages (V := K) (T := L) :=
  (binaryCentralImageFibreEquiv (MonoidHom.snd (Multiplicative K) Y) L).trans
    ((binarySplitPreimageEquiv (K := K) L).mapSubgroup.toEquiv.subtypeEquiv (fun H => by
      change H.map (binaryCentralRestrictedProjection (MonoidHom.snd (Multiplicative K) Y) L) = ⊤ ↔
        (H.map (binarySplitPreimageEquiv (K := K) L).toMonoidHom).map
          (MonoidHom.snd (Multiplicative K) L) = ⊤
      rw [Subgroup.map_map]
      rfl))

include e in
/-- Comparison for every exact exterior image, before applying any outer
full-projection, survival or weight restriction. -/
theorem binaryCentralImage_card_le_split (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [Finite Y] [Finite K] (L : Subgroup Y) :
    Nat.card {H : Subgroup X // H.map π = L} ≤
      Nat.card {H : Subgroup (Multiplicative K × Y) //
        H.map (MonoidHom.snd (Multiplicative K) Y) = L} := by
  rw [Nat.card_congr (binaryCentralImageFibreEquiv π L),
    Nat.card_congr (binarySplitImageFibreEquiv (K := K) L)]
  exact binaryCentralFull_card_le_split (binaryCentralRestrictedProjection π L)
    (binaryCentralRestrictedKernel π e L) (binaryCentralRestrictedProjection_surjective π hπ L)
    (binaryCentralRestrictedKernel_central π hc L)

/-- A literal partition by the exact exterior subgroup and any desired
predicate on that subgroup. -/
def binarySubgroupImagePartition (P : Subgroup Y → Prop) :
    {H : Subgroup X // P (H.map π)} ≃
      Σ L : {L : Subgroup Y // P L}, {H : Subgroup X // H.map π = L.1} where
  toFun H := ⟨⟨H.1.map π,H.2⟩,⟨H.1,rfl⟩⟩
  invFun L := ⟨L.2.1,by rw [L.2.2]; exact L.1.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨L,hL⟩,⟨H,hH⟩⟩; cases hH; rfl

include e in
/-- Central binary extensions have no more actual subgroups than the split
extension, retaining an arbitrary condition on the exact exterior image.
This supplies the comparison step used when replacing C4 coordinates. -/
theorem binaryCentral_filtered_card_le_split (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [Finite X] [Finite Y] [Finite K]
    (P : Subgroup Y → Prop) :
    Nat.card {H : Subgroup X // P (H.map π)} ≤
      Nat.card {H : Subgroup (Multiplicative K × Y) //
        P (H.map (MonoidHom.snd (Multiplicative K) Y))} := by
  letI : Fintype {L : Subgroup Y // P L} := Fintype.ofFinite _
  rw [Nat.card_congr (binarySubgroupImagePartition π P),Nat.card_sigma,
    Nat.card_congr (binarySubgroupImagePartition (MonoidHom.snd (Multiplicative K) Y) P),
    Nat.card_sigma]
  apply Finset.sum_le_sum
  intro L _
  exact binaryCentralImage_card_le_split π e hπ hc L.1

include e in
/-- Original nonnegative exterior weights are carried through the exact
image fibres, without changing action or normalizer weights. -/
theorem binaryCentral_weighted_image_count_le_split (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center X) [Finite Y] [Finite K]
    (w : Subgroup Y → ℝ) (hw : ∀ L, 0 ≤ w L) :
    ∑ L : Subgroup Y, w L * (Nat.card {H : Subgroup X // H.map π = L} : ℝ) ≤
      ∑ L : Subgroup Y, w L *
        (Nat.card {H : Subgroup (Multiplicative K × Y) //
          H.map (MonoidHom.snd (Multiplicative K) Y) = L} : ℝ) := by
  apply Finset.sum_le_sum
  intro L _
  apply mul_le_mul_of_nonneg_left _ (hw L)
  exact_mod_cast binaryCentralImage_card_le_split π e hπ hc L


end SymmetricSubgroupAsymptotics
