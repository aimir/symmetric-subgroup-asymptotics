import SymmetricSubgroupAsymptotics.QuotientSectionSubgroups
import SymmetricSubgroupAsymptotics.SquareLiftFibres

/-!
# Restrict an exact original image/kernel fibre to its literal preimage

The existing image-restriction equivalence in SquareLiftFibres is fully
general: its statement assumes no binary, central, or square condition.
This interface reuses that exact equivalence and composes it with the new
section classification, retaining the original subgroup on reconstruction.
Only normality inside the image preimage is required for the quotient;
normality in the whole original ambient group is not imposed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G Q : Type*} [Group G] [Group Q]

abbrev FixedImageKernelSubgroupFibre (θ : G →* Q) (B : Subgroup Q) (N : Subgroup G) :=
  ImageSquareLiftFibre θ B N

/-- The literal image B remains the target, and the entire original
kernel intersection N is retained in its original preimage. -/
def fixedImageKernelSubgroupEquiv (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) :
    FixedImageKernelSubgroupFibre θ B N ≃
      FixedKernelSubgroupFibre (θ.subgroupComap B) (N.subgroupOf (B.comap θ)) :=
  imageSquareLiftFibreEquiv θ B N hN

@[simp] theorem fixedImageKernelSubgroupEquiv_apply_val (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) (H : FixedImageKernelSubgroupFibre θ B N) :
    (fixedImageKernelSubgroupEquiv θ B N hN H).1 = H.1.subgroupOf (B.comap θ) := rfl

@[simp] theorem fixedImageKernelSubgroupEquiv_symm_val (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker)
    (L : FixedKernelSubgroupFibre (θ.subgroupComap B) (N.subgroupOf (B.comap θ))) :
    ((fixedImageKernelSubgroupEquiv θ B N hN).symm L).1 =
      L.1.map (B.comap θ).subtype := rfl

theorem imageKernel_le_restrictedKernel (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) :
    N.subgroupOf (B.comap θ) ≤ (θ.subgroupComap B).ker := by
  intro x hx
  apply Subtype.ext
  exact hN hx

/-- Compose both exact classifications. The quotient is by the original
intersection inside the literal preimage of B, without an ambient
normality or lift-existence premise. -/
def fixedImageKernelLiftEquiv (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) [(N.subgroupOf (B.comap θ)).Normal] :
    FixedImageKernelSubgroupFibre θ B N ≃
      HomomorphicLift (QuotientGroup.lift (N.subgroupOf (B.comap θ)) (θ.subgroupComap B)
        (imageKernel_le_restrictedKernel θ B N hN)) (MonoidHom.id B) :=
  (fixedImageKernelSubgroupEquiv θ B N hN).trans
    (fixedKernelLiftEquiv (θ.subgroupComap B) (N.subgroupOf (B.comap θ))
      (imageKernel_le_restrictedKernel θ B N hN))

/-- Complete original reconstruction: quotient preimage, then the
original inclusion in G. No subgroup, source, or label is counted twice. -/
@[simp] theorem fixedImageKernelLiftEquiv_symm_val (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) [(N.subgroupOf (B.comap θ)).Normal]
    (s : HomomorphicLift (QuotientGroup.lift (N.subgroupOf (B.comap θ)) (θ.subgroupComap B)
      (imageKernel_le_restrictedKernel θ B N hN)) (MonoidHom.id B)) :
    ((fixedImageKernelLiftEquiv θ B N hN).symm s).1 =
      (s.1.range.comap (QuotientGroup.mk' (N.subgroupOf (B.comap θ)))).map
        (B.comap θ).subtype := rfl

/-- A predicate remains a predicate on the decoded original G-subgroup. -/
def fixedImageKernelLiftRestrictedEquiv (θ : G →* Q) (B : Subgroup Q)
    (N : Subgroup G) (hN : N ≤ θ.ker) [(N.subgroupOf (B.comap θ)).Normal]
    (P : Subgroup G → Prop) :
    {H : FixedImageKernelSubgroupFibre θ B N // P H.1} ≃
      {s : HomomorphicLift (QuotientGroup.lift (N.subgroupOf (B.comap θ)) (θ.subgroupComap B)
        (imageKernel_le_restrictedKernel θ B N hN)) (MonoidHom.id B) //
        P ((s.1.range.comap (QuotientGroup.mk' (N.subgroupOf (B.comap θ)))).map
          (B.comap θ).subtype)} :=
  (fixedImageKernelLiftEquiv θ B N hN).subtypeEquiv (fun H => by
    change P H.1 ↔ P (((fixedImageKernelLiftEquiv θ B N hN).symm
      (fixedImageKernelLiftEquiv θ B N hN H)).1)
    rw [Equiv.symm_apply_apply])

end SymmetricSubgroupAsymptotics

end
