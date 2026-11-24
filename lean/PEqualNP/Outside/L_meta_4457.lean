import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4457

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Prefix induction as in the project's LowMergeWires proof.
lemma suffix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, he, ht⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [ht]⟩
    rw [List.foldl_cons, he]
    simp [step]

lemma addOne {n k : ℕ} {f : (Fin n → Bool) → Bool} (i : Fin n) (hf : HasCircuitSize n f k) :
    HasCircuitSize n (fun x => x i || f x) (k + 1) := by
  obtain ⟨c, hc, hs, he⟩ := hf
  let g : Gate := ⟨.or, [i.val, c.output]⟩
  refine ⟨⟨c.gates ++ [g], n + c.gates.length⟩, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hc h hh
    · obtain rfl := List.mem_singleton.mp hh
      simp [g]
  · simpa [Circuit.size] using Nat.succ_le_succ hs
  · intro x
    let w := c.wires (List.ofFn x)
    obtain ⟨t, ht, hl⟩ := suffix c.gates (List.ofFn x)
    change w = List.ofFn x ++ t at ht
    have len : w.length = n + c.gates.length := by simp [ht, hl]
    have inp : w.getD i false = x i := by
      rw [ht, List.getD_append _ _ _ _ (by simp)]
      simp
    have out : w.getD c.output false = f x := he x
    change ((c.gates ++ [g]).foldl step (List.ofFn x)).getD _ false = _
    rw [List.foldl_append]
    change (w ++ [GateOp.or.eval (([i.val, c.output] : List ℕ).map fun j => w.getD j false)]).getD (n + c.gates.length) false = _
    rw [← len, List.getD_append_right _ _ _ _ (le_refl _)]
    simpa [GateOp.eval] using congrArg₂ (· || ·) inp out

end PEqualNP.Outside.L_meta_4457

open PEqualNP.Outside.L_meta_4457

theorem PEqualNP.Outside.L_meta_4457 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true) || x3 x6) (x4 + x2.card) := by
  intro n s f k hf
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | @insert a s ha ih =>
    have eqn (x : Fin n → Bool) : decide (∃ j ∈ insert a s, x j = true) =
        (x a || decide (∃ j ∈ s, x j = true)) := by simp
    simpa [Finset.card_insert_of_notMem ha, Nat.add_assoc, eqn, Bool.or_assoc] using addOne a ih
