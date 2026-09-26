import SymmetricSubgroupAsymptotics.BinaryPairSharedAcceptance
import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry

/-! Complete independent sparse-coordinate and top registries install a
finite entry for every original normal subgroup. Only the explicitly
exceptional literal axes need a character or marked carrier resolution. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {H I J κ : Type} [Group H] {w k q r : ℕ}
    {U : Subgroup (Equiv.Perm (Fin w))}
    (F : BinaryPairFrame U (Fin k))
    (ρ : Representation (ZMod 2) H (Fin k → ZMod 2))
    (e : H ≃* F.top.range)
    (he : ∀ g v, ρ g v=F.coordinateTopAction (e g) v)
    (K : Subrepresentation ρ) (hK : K.toSubmodule=F.kernelSpace)
    (axes cuts fixed : I → Subrepresentation ρ)
    (hcuts : ∀ i, BinaryCoordinateCutData ρ K (axes i) (cuts i) (fixed i))

include e he hK hcuts in
/-- All original normals are covered by the complete shared registries.
The exceptional premise is restricted to an explicitly exceptional axis;
the good-cell pair certificate and its physical width are derived. -/
theorem shared_complete_finite_entry
    (haxes : ∀ W : Subrepresentation ρ, W.toSubmodule≤K.toSubmodule → ∃ i, axes i=W)
    (tops : J → BinaryTopKernelData H)
    (htops : ∀ T : Subgroup H, T.Normal → ∃ j, (tops j).kernel=T)
    (exceptional : I → Prop)
    (hcells : ∀ i j, (tops j).degree+sharedCost ρ axes cuts fixed i<Nat.card (Fin w) ∨
      exceptional i ∧ (tops j).kernel=⊥)
    (generators : Fin r → U)
    (hgenerators : Subgroup.closure (Set.range generators)=⊤)
    (carriers : κ → CheckedPermutationCarrier w q)
    (hresolve : ∀ (N : Subgroup U) [N.Normal],
      (∃ i, exceptional i ∧ N=F.coordinateSubgroup (axes i).toSubmodule) →
        Nonempty (BinaryNormalCharacterCriterion (U ⧸ N) w) ∨
        ∃ c, (carriers c).source=U ∧ (carriers c).axis=N.map U.subtype)
    (N : Subgroup U) [N.Normal] : BinaryFiniteEntry carriers U N := by
  rcases F.shared_complete_acceptance ρ e he K hK axes cuts fixed hcuts
    haxes tops htops exceptional hcells generators N with ⟨C,hwidth⟩ | hbad
  · exact Or.inl ⟨BinaryPhysicalPairCertificate.ofLocal F generators hgenerators C hwidth⟩
  · exact Or.inr (hresolve N hbad)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
