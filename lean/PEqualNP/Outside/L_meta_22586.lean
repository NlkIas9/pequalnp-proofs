import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22586_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩,
     ⟨.or, [3, 6]⟩,
     ⟨.or, [2, 7]⟩,
     ⟨.and, [0, 8]⟩,
     ⟨.not, [7]⟩,
     ⟨.and, [1, 10]⟩,
     ⟨.or, [9, 11]⟩], 12⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22586_aux

open PEqualNP.Outside.L_meta_22586_aux in
theorem PEqualNP.Outside.L_meta_22586 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (446 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
