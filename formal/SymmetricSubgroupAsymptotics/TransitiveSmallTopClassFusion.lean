import SymmetricSubgroupAsymptotics.SmallPrimeTopBlockClassFusion
import SymmetricSubgroupAsymptotics.SymmetricTopThreeBlockClassFusion

/-! A finite cover of the C2, C3 and S3 top cases for actual binary and
ternary block actions. Prime proper three-point top order is forced by
transitivity and Lagrange, with no supplied classification or class bound.
The actual original group and all kernel correlations are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveSmallTopClassFusion
open OriginalBlockClassBound SmallPrimeTopBlockClassFusion SymmetricTopThreeBlockClassFusion
variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem degree_le_top_card {X:Type} [Finite X] [MulAction A X]
    [MulAction.IsPretransitive A X] (x₀:X) : Nat.card X≤Nat.card (Top (A:=A) (X:=X)) := by
  let g : X→A := fun x=>Classical.choose (MulAction.exists_smul_eq A x₀ x)
  have hg (x:X) : g x•x₀=x := Classical.choose_spec (MulAction.exists_smul_eq A x₀ x)
  let t : X→Top (A:=A) (X:=X) := fun x=>⟨topMap (A:=A) (X:=X) (g x),⟨g x,rfl⟩⟩
  apply Nat.card_le_card_of_injective t
  intro x y he
  have h := congrArg (fun u:Top (A:=A) (X:=X)=>(u:Equiv.Perm X) x₀) he
  have h' : g x•x₀=g y•x₀ := h
  exact (hg x).symm.trans (h'.trans (hg y))

theorem two_top_card [MulAction A (Fin 2)] [MulAction.IsPretransitive A (Fin 2)] :
    Nat.card (Top (A:=A) (X:=Fin 2))=2 := by
  have hlo := degree_le_top_card (A:=A) (0:Fin 2)
  have hhi := (Top (A:=A) (X:=Fin 2)).card_le_card_group
  have hperm : Nat.card (Equiv.Perm (Fin 2))=2 := by rw [Nat.card_perm,Nat.card_fin]; rfl
  rw [hperm] at hhi
  rw [Nat.card_fin] at hlo
  exact Nat.le_antisymm hhi hlo

theorem proper_three_top_card [MulAction A (Fin 3)] [MulAction.IsPretransitive A (Fin 3)]
    (hproper:Top (A:=A) (X:=Fin 3)≠⊤) : Nat.card (Top (A:=A) (X:=Fin 3))=3 := by
  let T := Top (A:=A) (X:=Fin 3)
  have hlo : 3≤Nat.card T := by simpa only [Nat.card_fin] using degree_le_top_card (A:=A) (0:Fin 3)
  have hindex : 2≤T.index := T.one_lt_index_of_ne_top hproper
  have hcard := T.card_mul_index
  have hperm : Nat.card (Equiv.Perm (Fin 3))=6 := by rw [Nat.card_perm,Nat.card_fin]; rfl
  rw [hperm] at hcard
  nlinarith [Nat.mul_le_mul_left (Nat.card T) hindex]

variable {Ω:Type} [MulAction A Ω] [Finite Ω] [FaithfulSMul A Ω]

section Two
variable [MulAction A (Fin 2)] [MulAction.IsPretransitive A (Fin 2)]
    (b:Ω→Fin 2) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_two_blocks (hsize:∀x,Nat.card (originalBlockFibre b x)≤2) :
    Nat.card (ConjClasses A)≤5 :=
  binary_two_top_class_card_le_five b hb two_top_card hsize

include hb in
theorem ternary_two_blocks (hsize:∀x,Nat.card (originalBlockFibre b x)≤3) :
    Nat.card (ConjClasses A)≤13 :=
  ternary_two_top_class_card_le_thirteen b hb two_top_card hsize
end Two

section Three
variable [MulAction A (Fin 3)] [MulAction.IsPretransitive A (Fin 3)]
    (b:Ω→Fin 3) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_three_blocks (hsize:∀x,Nat.card (originalBlockFibre b x)≤2) :
    Nat.card (ConjClasses A)≤10 := by
  by_cases ht : Top (A:=A) (X:=Fin 3)=⊤
  · exact binary_full_top_class_card_le_ten b hb ht hsize
  · exact (binary_three_top_class_card_le_eight b hb (proper_three_top_card ht) hsize).trans (by decide)

include hb in
theorem ternary_three_blocks (hsize:∀x,Nat.card (originalBlockFibre b x)≤3) :
    Nat.card (ConjClasses A)≤66 := by
  by_cases ht : Top (A:=A) (X:=Fin 3)=⊤
  · exact ternary_full_top_class_card_le_sixtySix b hb ht hsize
  · exact (ternary_three_top_class_card_le_twentyFive b hb (proper_three_top_card ht) hsize).trans (by decide)
end Three

end SymmetricSubgroupAsymptotics.TransitiveSmallTopClassFusion
