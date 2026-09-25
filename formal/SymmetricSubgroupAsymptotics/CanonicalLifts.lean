import SymmetricSubgroupAsymptotics.GaussianCount

/-!
# Exact counting of canonical lifts through a binary quotient

The inverse images of the actual binary subspaces are precisely the actual
subgroups containing the quotient kernel. This counts canonical lifts on one
fixed action, before labelling profiles or counting noncanonical lifts.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Binary subspaces and subgroups of the corresponding elementary abelian
group are the same objects, including their order relation. -/
def binarySubmoduleSubgroupOrderIso (r : ℕ) :
    Submodule (ZMod 2) (Fin r → ZMod 2) ≃o
      Subgroup (Multiplicative (Fin r → ZMod 2)) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup

/-- The subgroup correspondence for an arbitrary surjective group map. -/
def subgroupComapOrderIso {G Q : Type*} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π) :
    Subgroup Q ≃o {H : Subgroup G // π.ker ≤ H} where
  toFun U := ⟨U.comap π, by
    intro g hg
    change π g ∈ U
    rw [show π g = 1 from hg]
    exact U.one_mem⟩
  invFun H := H.1.map π
  left_inv U := Subgroup.map_comap_eq_self_of_surjective hπ U
  right_inv H := Subtype.ext (Subgroup.comap_map_eq_self H.2)
  map_rel_iff' := Subgroup.comap_le_comap_of_surjective hπ

/-- The canonical subgroup is the full inverse image of its quotient
subspace; the definition does not identify different subspaces. -/
def canonicalLift {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2))
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) : Subgroup G :=
  U.toAddSubgroup.toSubgroup.comap π

theorem ker_le_canonicalLift {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2))
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) : π.ker ≤ canonicalLift π U := by
  intro g hg
  change (π g).toAdd ∈ U
  rw [show π g = 1 from hg]
  exact U.zero_mem

/-- The exact canonical-lift correspondence, independent of the ambient
group's finiteness, commutativity or permutation representation. -/
def canonicalLiftOrderIso {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π) :
    Submodule (ZMod 2) (Fin r → ZMod 2) ≃o {H : Subgroup G // π.ker ≤ H} :=
  (binarySubmoduleSubgroupOrderIso r).trans (subgroupComapOrderIso π hπ)

@[simp] theorem canonicalLiftOrderIso_apply {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    (canonicalLiftOrderIso π hπ U).1 = canonicalLift π U := rfl

theorem canonicalLift_injective {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π) :
    Function.Injective (canonicalLift π) := by
  intro U W h
  exact (canonicalLiftOrderIso π hπ).injective (Subtype.ext h)

@[simp] theorem canonicalLift_map {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    (canonicalLift π U).map π = U.toAddSubgroup.toSubgroup :=
  Subgroup.map_comap_eq_self_of_surjective hπ _

/-- The actual subgroups containing the binary quotient kernel number
exactly the actual binary subspaces. -/
theorem canonicalLift_count {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π) :
    Nat.card {H : Subgroup G // π.ker ≤ H} = binarySubspaceCount r :=
  (Nat.card_congr (canonicalLiftOrderIso π hπ).toEquiv).symm

/-- The canonical count in the approved explicit Gaussian normalization. -/
theorem canonicalLift_count_eq_gaussianSum {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π) :
    (Nat.card {H : Subgroup G // π.ker ≤ H} : ℚ) = binaryGaussianSum r := by
  rw [canonicalLift_count π hπ]
  exact binarySubspaceCount_eq_gaussianSum r

/-- A quotient-coordinate image of a canonical lift is exactly the
corresponding image of the chosen subspace. -/
theorem canonicalLift_map_comp {G Q : Type*} [Group G] [Group Q] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (f : Multiplicative (Fin r → ZMod 2) →* Q)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    (canonicalLift π U).map (f.comp π) = U.toAddSubgroup.toSubgroup.map f := by
  rw [← Subgroup.map_map, canonicalLift_map π hπ]

/-- For a subgroup retaining the whole kernel, fullness can be read in the
quotient. No Frattini or generation hypothesis is needed in this case. -/
theorem map_eq_top_iff_of_ker_le {G Q : Type*} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π) (H : Subgroup G) (hH : π.ker ≤ H) :
    H.map π = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    have hc := Subgroup.comap_map_eq_self hH
    rw [h, Subgroup.comap_top] at hc
    exact hc.symm
  · rintro rfl
    exact Subgroup.map_top_of_surjective π hπ

/-- A commuting quotient square transports full projection to an actual
factor whenever the product kernel covers that factor's quotient kernel. -/
theorem canonicalLift_full_projection_iff {G D Q : Type*}
    [Group G] [Group D] [Group Q] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (p : G →* D) (q : D →* Q) (hq : Function.Surjective q)
    (f : Multiplicative (Fin r → ZMod 2) →* Q)
    (hcomm : q.comp p = f.comp π) (hker : q.ker ≤ π.ker.map p)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    (canonicalLift π U).map p = ⊤ ↔ U.toAddSubgroup.toSubgroup.map f = ⊤ := by
  have hk : q.ker ≤ ((canonicalLift π U).map p) :=
    hker.trans (Subgroup.map_mono (ker_le_canonicalLift π U))
  rw [← map_eq_top_iff_of_ker_le q hq _ hk, Subgroup.map_map, hcomm,
    canonicalLift_map_comp π hπ]

/-- Restricting the canonical correspondence preserves any condition on
the actual subgroup; the kernel condition remains explicit. -/
def canonicalLiftFilterEquiv {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (P : Subgroup G → Prop) :
    {U : Submodule (ZMod 2) (Fin r → ZMod 2) // P (canonicalLift π U)} ≃
      {H : Subgroup G // π.ker ≤ H ∧ P H} where
  toFun U := ⟨canonicalLift π U.1, ker_le_canonicalLift π U.1, U.2⟩
  invFun H := ⟨(canonicalLiftOrderIso π hπ).symm ⟨H.1, H.2.1⟩, by
    have he := congrArg Subtype.val ((canonicalLiftOrderIso π hπ).apply_symm_apply
      ⟨H.1, H.2.1⟩)
    change canonicalLift π ((canonicalLiftOrderIso π hπ).symm ⟨H.1, H.2.1⟩) = H.1 at he
    rw [he]
    exact H.2.2⟩
  left_inv U := Subtype.ext ((canonicalLiftOrderIso π hπ).symm_apply_apply U.1)
  right_inv H := by
    apply Subtype.ext
    exact congrArg (fun S : {S : Subgroup G // π.ker ≤ S} => S.1)
      ((canonicalLiftOrderIso π hπ).apply_symm_apply ⟨H.1, H.2.1⟩)

/-- Exact canonical counting with all actual coordinate-projection
requirements retained simultaneously. This does not count exceptional lifts. -/
theorem canonicalLift_full_count {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    {ι : Type*} (D Q : ι → Type*) [∀ i, Group (D i)] [∀ i, Group (Q i)]
    (p : ∀ i, G →* D i) (q : ∀ i, D i →* Q i) (hq : ∀ i, Function.Surjective (q i))
    (f : ∀ i, Multiplicative (Fin r → ZMod 2) →* Q i)
    (hcomm : ∀ i, (q i).comp (p i) = (f i).comp π)
    (hker : ∀ i, (q i).ker ≤ π.ker.map (p i)) :
    Nat.card {H : Subgroup G // π.ker ≤ H ∧ ∀ i, H.map (p i) = ⊤} =
      Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
        ∀ i, U.toAddSubgroup.toSubgroup.map (f i) = ⊤} := by
  calc
    _ = Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
        ∀ i, (canonicalLift π U).map (p i) = ⊤} :=
      (Nat.card_congr (canonicalLiftFilterEquiv π hπ (fun H => ∀ i, H.map (p i) = ⊤))).symm
    _ = _ := Nat.card_congr (Equiv.subtypeEquivRight fun U =>
      forall_congr' fun i => canonicalLift_full_projection_iff π hπ (p i) (q i) (hq i)
        (f i) (hcomm i) (hker i) U)

/-- Faithful permutation transport preserves distinct canonical lifts as
distinct literal subgroups, without taking conjugacy classes. -/
theorem canonicalLift_permutation_injective {G : Type*} [Group G] {r n : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    (action : G →* Equiv.Perm (Fin n)) (haction : Function.Injective action) :
    Function.Injective (fun U => (canonicalLift π U).map action) :=
  (Subgroup.map_injective haction).comp (canonicalLift_injective π hπ)

end SymmetricSubgroupAsymptotics
