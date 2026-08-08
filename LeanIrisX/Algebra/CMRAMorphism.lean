import LeanIrisX.Algebra.CMRA
import LeanIrisX.Core.Morphism

/-! Morphisms that preserve the resource algebra and step-indexed validity. -/

namespace LeanIrisX

structure CMRAHom (α : Type u) (β : Type v)
    [OFE α] [CMRA α] [OFE β] [CMRA β] extends α -n> β where
  validN_map : ∀ {n x}, CMRA.validN n x → CMRA.validN n (toFun x)
  op_map : ∀ x y, toFun (CMRA.op x y) = CMRA.op (toFun x) (toFun y)

infixr:25 " -c> " => CMRAHom

instance {α : Type u} {β : Type v} [OFE α] [CMRA α] [OFE β] [CMRA β] :
    CoeFun (α -c> β) (fun _ => α → β) := ⟨fun f => f.toFun⟩

namespace CMRAHom

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OFE α] [CMRA α] [OFE β] [CMRA β] [OFE γ] [CMRA γ]

theorem includedN_map (f : α -c> β) {n : Nat} {x y : α}
    (h : CMRA.IncludedN n x y) : CMRA.IncludedN n (f x) (f y) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨f z, ?_⟩
  exact OFE.trans (f.nonExpansive n hz) (OFE.of_eq (f.op_map x z))

def id : α -c> α where
  toFun x := x
  nonExpansive := NonExpansive.id
  validN_map h := h
  op_map _ _ := rfl

def comp (g : β -c> γ) (f : α -c> β) : α -c> γ where
  toFun x := g (f x)
  nonExpansive := NonExpansive.comp g.nonExpansive f.nonExpansive
  validN_map h := g.validN_map (f.validN_map h)
  op_map x y := by rw [f.op_map, g.op_map]

end CMRAHom
end LeanIrisX
