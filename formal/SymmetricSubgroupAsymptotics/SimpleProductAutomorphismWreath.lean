import SymmetricSubgroupAsymptotics.SimpleProductAutomorphismCoordinates
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! The actual automorphism group of a finite power of a nonabelian simple
group is its coordinate-automorphism wreath product. All coordinate maps
are obtained from the original automorphism. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SimpleProductAutomorphismWreath

variable {I T : Type} [Group T]

abbrev Wreath (T I : Type) [Group T] :=
  PermutationalWreathProduct (MulAut T) (Equiv.Perm I) I

/-- The original product-coordinate automorphism, with the top permuting
coordinates and the base acting separately on the original factors. -/
def action (w : Wreath T I) : MulAut (I → T) where
  toFun x i := w.left i (x (w.right.symm i))
  invFun y i := (w.left (w.right i)).symm (y (w.right i))
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_mul' x y := by funext i; exact map_mul _ _ _

@[simp] theorem action_apply (w : Wreath T I) (x : I → T) (i : I) :
    action w x i = w.left i (x (w.right.symm i)) := rfl

/-- This is a group homomorphism for the actual semidirect multiplication. -/
def actionHom : Wreath T I →* MulAut (I → T) where
  toFun := action
  map_one' := by ext x i; rfl
  map_mul' a b := by
    ext x i
    rfl

theorem action_injective [Nontrivial T] :
    Function.Injective (actionHom (I := I) (T := T)) := by
  intro a b he
  have h (x : I → T) (i : I) :
      a.left i (x (a.right.symm i)) = b.left i (x (b.right.symm i)) :=
    congrFun (congrArg (fun f : MulAut (I → T) => f x) he) i
  have hrightSymm : a.right.symm = b.right.symm := by
    ext i
    by_contra hn
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    have hi := h (Pi.mulSingle (a.right.symm i) t) i
    simp only [Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (Ne.symm hn), map_one] at hi
    exact ht ((a.left i).injective (hi.trans (map_one _).symm))
  have hright : a.right = b.right := by
    simpa only [Equiv.symm_symm] using congrArg Equiv.symm hrightSymm
  apply PermutationalWreathProduct.ext ?_ hright
  funext i
  apply MulEquiv.ext
  intro t
  have hi := h (fun _ => t) i
  exact hi

theorem action_surjective [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) :
    Function.Surjective (actionHom (I := I) (T := T)) := by
  intro e
  obtain ⟨q, a, ha⟩ :=
    SimpleProductAutomorphismCoordinates.automorphism_coordinates hT e
  refine ⟨⟨a, q⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  funext i
  exact (ha x i).symm

/-- No classification premise is used in this exact automorphism theorem. -/
def equiv [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) : MulAut (I → T) ≃* Wreath T I :=
  (MulEquiv.ofBijective actionHom ⟨action_injective, action_surjective hT⟩).symm

def routingHom [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) : MulAut (I → T) →* Equiv.Perm I :=
  PermutationalWreathProduct.rightHom.comp (equiv hT).toMonoidHom

theorem coordinateFormula [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (e : MulAut (I → T)) (x : I → T) (i : I) :
    e x i = (equiv hT e).left i (x ((routingHom hT e).symm i)) := by
  have h := congrFun
    (congrArg (fun f : MulAut (I → T) => f x) ((equiv hT).symm_apply_apply e)) i
  exact h.symm

def innerCoordinates (x : I → T) : Wreath T I :=
  ⟨fun i => MulAut.conj (x i), 1⟩

theorem action_inner (x : I → T) :
    actionHom (innerCoordinates x) = MulAut.conj x := by
  ext y i
  rfl

theorem equiv_inner [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (x : I → T) :
    equiv hT (MulAut.conj x) = innerCoordinates x := by
  apply (equiv hT).symm.injective
  rw [(equiv hT).symm_apply_apply]
  exact (action_inner x).symm

theorem routing_conj [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (x : I → T) :
    routingHom hT (MulAut.conj x) = 1 := by
  change (equiv hT (MulAut.conj x)).right = 1
  rw [equiv_inner]
  rfl

end SymmetricSubgroupAsymptotics.SimpleProductAutomorphismWreath
