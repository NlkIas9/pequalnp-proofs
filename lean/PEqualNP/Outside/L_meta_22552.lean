import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22552_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩,
     ⟨.or, [6, 5]⟩,
     ⟨.not, [7]⟩,
     ⟨.and, [1, 8]⟩,
     ⟨.and, [2, 3]⟩,
     ⟨.and, [0, 4]⟩,
     ⟨.or, [9, 10]⟩,
     ⟨.or, [12, 11]⟩], 13⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22552_aux

open PEqualNP.Outside.L_meta_22552_aux in
theorem PEqualNP.Outside.L_meta_22552 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33680 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
