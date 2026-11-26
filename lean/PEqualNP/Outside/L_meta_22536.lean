import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22536_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩,
     ⟨.and, [2, 3]⟩,
     ⟨.or, [0, 1]⟩,
     ⟨.or, [2, 3]⟩,
     ⟨.and, [8, 9]⟩,
     ⟨.or, [7, 10]⟩,
     ⟨.or, [6, 11]⟩], 12⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22536_aux

open PEqualNP.Outside.L_meta_22536_aux in
theorem PEqualNP.Outside.L_meta_22536 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
