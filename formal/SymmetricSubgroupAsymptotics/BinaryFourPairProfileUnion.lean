import SymmetricSubgroupAsymptotics.BinaryFourPairProfileIncidence

/-!
# Common-label unions for the four-pair/E8 profile move

Profiles record the pair count before fusion, the E8 count before fusion,
and every untouched residual multiplicity.  Source and target multiplicity
maps are both injective.  Hence forgetting the profile index on a common
labelled point set counts every actual subgroup exactly once on either side.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairProfileUnion

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev Profile := (ℕ × ℕ) × (α → ℕ)

def sourceMultiplicity (t : Profile (α := α)) :
    PUnit.{1} ⊕ BinaryPairE8Profile.ExteriorIndex (α := α) → ℕ :=
  RepeatedMarkerMergedProfile.multiplicity
    (BinaryPairE8Profile.exteriorMultiplicity t.2 t.1.2) (t.1.1+4)

def targetMultiplicity (t : Profile (α := α)) :
    PUnit.{1} ⊕ BinaryPairE8Profile.ExteriorIndex (α := α) → ℕ :=
  RepeatedMarkerMergedProfile.multiplicity
    (BinaryPairE8Profile.exteriorMultiplicity t.2 (t.1.2+1)) t.1.1

theorem sourceMultiplicity_injective :
    Function.Injective (sourceMultiplicity (α := α)) := by
  intro t s h
  apply Prod.ext
  · apply Prod.ext
    · have hp := congrFun h (.inl PUnit.unit)
      change t.1.1+4 = s.1.1+4 at hp
      omega
    · have he := congrFun h (.inr (.inl PUnit.unit))
      exact he
  · funext a
    exact congrFun h (.inr (.inr a))

theorem targetMultiplicity_injective :
    Function.Injective (targetMultiplicity (α := α)) := by
  intro t s h
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun h (.inl PUnit.unit)
    · have he := congrFun h (.inr (.inl PUnit.unit))
      change t.1.2+1 = s.1.2+1 at he
      omega
  · funext a
    exact congrFun h (.inr (.inr a))

abbrev FullPoints := RepeatedMarkerMergedProfile.points
  (BinaryPairE8Profile.exteriorPoints Ω)

abbrev FullAction := RepeatedMarkerMergedProfile.action
  (BinaryPairE8Profile.exteriorPoints Ω)
  (BinaryPairE8Profile.exteriorAction Ω U)

abbrev SourcePhysicalOn (t : Profile (α := α)) (X : Type) :=
  AssembledOrbitProfileOn
    (OrbitProfileFull (FullAction Ω U) (m := sourceMultiplicity t) 1) X

abbrev TargetPhysicalOn (t : Profile (α := α)) (X : Type) :=
  AssembledOrbitProfileOn
    (OrbitProfileFull (FullAction Ω U) (m := targetMultiplicity t) 1) X

local instance sourcePhysicalOnFinite (t : Profile (α := α)) (X : Type) [Finite X] :
    Finite (SourcePhysicalOn Ω U t X) :=
  Finite.of_injective
    (fun H : SourcePhysicalOn Ω U t X => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance sourcePhysicalOnFintype (t : Profile (α := α)) (X : Type) [Finite X] :
    Fintype (SourcePhysicalOn Ω U t X) := Fintype.ofFinite _

local instance targetPhysicalOnFinite (t : Profile (α := α)) (X : Type) [Finite X] :
    Finite (TargetPhysicalOn Ω U t X) :=
  Finite.of_injective
    (fun H : TargetPhysicalOn Ω U t X => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance targetPhysicalOnFintype (t : Profile (α := α)) (X : Type) [Finite X] :
    Fintype (TargetPhysicalOn Ω U t X) := Fintype.ofFinite _

abbrev SourceSelected (X : Type) (S : Finset (Profile (α := α))) :=
  AssembledOrbitProfilesOn
    (fun t : S => sourceMultiplicity t.val)
    (fun t => OrbitProfileFull (FullAction Ω U)
      (m := sourceMultiplicity t.val) 1) X

abbrev TargetSelected (X : Type) (S : Finset (Profile (α := α))) :=
  AssembledOrbitProfilesOn
    (fun t : S => targetMultiplicity t.val)
    (fun t => OrbitProfileFull (FullAction Ω U)
      (m := targetMultiplicity t.val) 1) X

local instance sourceSelectedFinite (X : Type) [Finite X]
    (S : Finset (Profile (α := α))) : Finite (SourceSelected Ω U X S) :=
  Finite.of_injective
    (fun H : SourceSelected Ω U X S => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance targetSelectedFinite (X : Type) [Finite X]
    (S : Finset (Profile (α := α))) : Finite (TargetSelected Ω U X S) :=
  Finite.of_injective
    (fun H : TargetSelected Ω U X S => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

def sourceSigmaEquiv (X : Type) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Σ t : S, SourcePhysicalOn Ω U t.val X) ≃ SourceSelected Ω U X S :=
  assembledOrbitProfilesSigmaEquiv
    (fun t s h => Subtype.ext (sourceMultiplicity_injective h))
    (fun _ _ h => h)
    (RepeatedMarkerMergedProfile.action_transitive
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U)
      (BinaryFourPairProfileIncidence.ext_transitive Ω U htrans))
    (RepeatedMarkerMergedProfile.action_separated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U) hsep
      (BinaryFourPairProfileIncidence.ext_degree_ne_two Ω hdegree))

def targetSigmaEquiv (X : Type) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Σ t : S, TargetPhysicalOn Ω U t.val X) ≃ TargetSelected Ω U X S :=
  assembledOrbitProfilesSigmaEquiv
    (fun t s h => Subtype.ext (targetMultiplicity_injective h))
    (fun _ _ h => h)
    (RepeatedMarkerMergedProfile.action_transitive
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U)
      (BinaryFourPairProfileIncidence.ext_transitive Ω U htrans))
    (RepeatedMarkerMergedProfile.action_separated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U) hsep
      (BinaryFourPairProfileIncidence.ext_degree_ne_two Ω hdegree))

theorem source_weight_sum (X : Type) [Finite X]
    (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (w : Subgroup (Equiv.Perm X) → ℚ) :
    (∑ H : SourceSelected Ω U X S, w H.val) =
      ∑ t : S, ∑ H : SourcePhysicalOn Ω U t.val X, w H.val := by
  calc
    _ = ∑ z : (Σ t : S, SourcePhysicalOn Ω U t.val X), w z.2.val :=
      (Fintype.sum_equiv (sourceSigmaEquiv Ω U X S htrans hsep hdegree)
        _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sigma _

theorem target_weight_sum (X : Type) [Finite X]
    (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated
      (BinaryPairE8Profile.exteriorPoints Ω)
      (BinaryPairE8Profile.exteriorAction Ω U))
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (w : Subgroup (Equiv.Perm X) → ℚ) :
    (∑ H : TargetSelected Ω U X S, w H.val) =
      ∑ t : S, ∑ H : TargetPhysicalOn Ω U t.val X, w H.val := by
  calc
    _ = ∑ z : (Σ t : S, TargetPhysicalOn Ω U t.val X), w z.2.val :=
      (Fintype.sum_equiv (targetSigmaEquiv Ω U X S htrans hsep hdegree)
        _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sigma _

end SymmetricSubgroupAsymptotics.BinaryFourPairProfileUnion
