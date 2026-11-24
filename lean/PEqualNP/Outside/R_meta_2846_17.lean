import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.MetaComplexity.SingleLevel

-- The first obligation is untyped: can two AND gates be nested in a least top-stuck circuit?
-- The second is graph-independent: an OR-only input cone and two monochromatic evaluations
-- label all operands of live products in a single-level circuit. The proof below orients
-- every product and assembles two global closed sets, even when an OR wire has many readers.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2846_17
    (normalize : ∀ (a b : ℕ) (I : Fin a → Fin b → Prop) [DecidableRel I] (C : Circuit)
      (f : (Fin (a+b) → Bool) → Bool),
      (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      IsAO2 (a+b) C → (∀ z, f z = decide (∃ p l, I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true)) →
      circuitFun (a+b) C = f → (∀ D, IsAO2 (a+b) D → circuitFun (a+b) D = f → C.size ≤ D.size) →
      (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        (a+b+i = C.output ∨ ∃ k ∈ T, ∀ j < C.gates.length, (a+b+i ∈ (gateAt C j).inputs ↔ j = k))) ∧
        ∀ w, (∀ z, (C.wires (List.ofFn z)).getD w false = true → f z = true) →
        (∃ k < C.gates.length, (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) →
        ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → k ∈ T) → IsSingleLevel (a+b) C)
    (certificate : ∀ (a b : ℕ) (C : Circuit), IsAO2 (a+b) C → IsSingleLevel (a+b) C →
      (∀ D, IsAO2 (a+b) D → circuitFun (a+b) D = circuitFun (a+b) C → C.size ≤ D.size) →
      (∀ k : Bool, circuitFun (a+b) C (fun i => decide (i.val < a) == k) = false) →
      ∃ (U : Finset ℕ) (c : ℕ → Bool → Bool),
      (∀ w < a+b, ∀ k, c w k = (decide (w < a) == k)) ∧
      (∀ w ∈ U, w < a+b ∨ ∃ i < C.gates.length, w = a+b+i ∧ (gateAt C i).op = GateOp.or ∧
        ∀ v ∈ (gateAt C i).inputs, v ∈ U) ∧
      (∀ i < C.gates.length, ∀ k, c (a+b+i) k = (gateAt C i).op.eval ((gateAt C i).inputs.map (fun u => c u k))) ∧
      ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → (∀ v ∈ (gateAt C i).inputs, v ∈ U) ∧ ∀ k, c (a+b+i) k = false) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  classical
  intro p l I inst C four ao spec least stuck
  let f : (Fin (p+l) → Bool) → Bool := fun z => decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)
  have exactF : circuitFun (p+l) C = f := funext spec
  have minimal : ∀ D, IsAO2 (p+l) D → circuitFun (p+l) D = f → C.size ≤ D.size := by
    intro D hD hf; exact least D hD (fun z => congrFun hf z)
  have hsingle : IsSingleLevel (p+l) C := by
    apply normalize p l I C f four ao (fun _ => rfl) exactF minimal
    obtain ⟨T, htree, hreader⟩ := stuck
    refine ⟨T,htree,?_⟩
    intro w hw hr
    exact hreader w (fun z hz => of_decide_eq_true (hw z hz)) hr
  have hfalse : ∀ k : Bool, circuitFun (p+l) C (fun i => decide (i.val < p) == k) = false := by
    intro k; rw [spec]; apply decide_eq_false
    rintro ⟨u,v,_,hu,hv⟩
    have hleft : (Fin.castAdd l u).val < p := u.isLt
    have hright : ¬ (Fin.natAdd p v).val < p := by change ¬ p + v.val < p; omega
    cases k
    · simp [hleft] at hu
    · simp [hright] at hv
  obtain ⟨U,c,hstart,origin,trace,hterm⟩ := certificate p l C ao hsingle (fun D hD h => minimal D hD (h.trans exactF)) hfalse
  let Pval := fun w => c w true
  let Lval := fun w => c w false
  have initial : ∀ w < p+l, (Pval w = true ↔ w < p) ∧ (Lval w = true ↔ p ≤ w) := by
    intro w hw; simp [Pval,Lval,hstart w hw]
  have binary : ∀ i < C.gates.length, ∃ a b, (gateAt C i).inputs = [a,b] ∧ a < p+l+i ∧ b < p+l+i := by
    intro i hi
    have hm : gateAt C i ∈ C.gates := by
      change C.gates.getD i ⟨GateOp.or, []⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ hm)
    exact ⟨a,b,hab,ao.2.1 i hi a (by simp [hab]),ao.2.1 i hi b (by simp [hab])⟩
  have orval : ∀ i < C.gates.length, ∀ a b, (gateAt C i).inputs = [a,b] → (gateAt C i).op = GateOp.or →
      Pval (p+l+i) = (Pval a || Pval b) ∧ Lval (p+l+i) = (Lval a || Lval b) := by
    intro i hi a b hab hop
    have opOr (x y : Bool) : GateOp.or.eval [x,y] = (x || y) := by cases x <;> cases y <;> rfl
    constructor
    · simpa only [Pval,hop,hab,List.map_cons,List.map_nil,opOr] using trace i hi true
    · simpa only [Lval,hop,hab,List.map_cons,List.map_nil,opOr] using trace i hi false
  have noMono : ∀ i < C.gates.length, ∀ a b, (gateAt C i).inputs = [a,b] → (gateAt C i).op = GateOp.and →
      a ∈ U ∧ b ∈ U ∧ ¬ (Pval a = true ∧ Pval b = true) ∧ ¬ (Lval a = true ∧ Lval b = true) := by
    intro i hi a b hab hop
    obtain ⟨hU,hz⟩ := hterm i hi hop
    have disj (k : Bool) : ¬ (c a k = true ∧ c b k = true) := by
      rintro ⟨ha,hb⟩; have h := hz k; rw [trace i hi k] at h
      rw [hab,hop] at h
      change GateOp.and.eval [c a k,c b k] = false at h
      rw [ha,hb] at h
      exact (by decide : true ≠ false) h
    exact ⟨hU a (by simp [hab]), hU b (by simp [hab]), disj true, disj false⟩
  have colored : ∀ w ∈ U, Pval w = true ∨ Lval w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      obtain hi | ⟨i, hi, rfl, hop, hchild⟩ := origin w hw
      · by_cases hp : w < p
        · exact Or.inl ((initial w hi).1.mpr hp)
        · exact Or.inr ((initial w hi).2.mpr (by omega))
      · obtain ⟨a,b,hab,ha,_⟩ := binary i hi
        have hmem := hchild a (by simp [hab])
        obtain hP | hL := ih a ha hmem
        · left; simp [(orval i hi a b hab hop).1, hP]
        · right; simp [(orval i hi a b hab hop).2, hL]
  let P := U.filter fun w => Lval w = false
  let L := U.filter fun w => Pval w = false
  refine ⟨P, L, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hw, hzero⟩ := Finset.mem_filter.mp hw
    obtain hi | ⟨i,hi,rfl,hop,hchild⟩ := origin w hw
    · left; by_contra! hn; exact Bool.false_ne_true (hzero.symm.trans ((initial w hi).2.mpr hn))
    · right; refine ⟨i,hi,rfl,hop,?_⟩
      obtain ⟨a,b,hab,_,_⟩ := binary i hi
      rw [(orval i hi a b hab hop).2, Bool.or_eq_false_iff] at hzero
      intro v hv; refine Finset.mem_filter.mpr ⟨hchild v hv,?_⟩
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hzero.1
      · exact hzero.2
  · intro w hw
    obtain ⟨hw, hzero⟩ := Finset.mem_filter.mp hw
    obtain hi | ⟨i,hi,rfl,hop,hchild⟩ := origin w hw
    · left; refine ⟨?_,hi⟩; by_contra! hn; exact Bool.false_ne_true (hzero.symm.trans ((initial w hi).1.mpr hn))
    · right; refine ⟨i,hi,rfl,hop,?_⟩
      obtain ⟨a,b,hab,_,_⟩ := binary i hi
      rw [(orval i hi a b hab hop).1, Bool.or_eq_false_iff] at hzero
      intro v hv; refine Finset.mem_filter.mpr ⟨hchild v hv,?_⟩
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hzero.1
      · exact hzero.2
  · intro i hi hop
    obtain ⟨a,b,hab,_,_⟩ := binary i hi
    obtain ⟨ha,hb,hnp,hnl⟩ := noMono i hi a b hab hop
    refine ⟨a,b,hab,?_⟩
    have hca := colored a ha
    have hcb := colored b hb
    simp only [P,L,Finset.mem_filter,ha,hb,true_and]
    rcases hca with haP | haL
    · have nb : Pval b ≠ true := fun h => hnp ⟨haP,h⟩
      have lb := hcb.resolve_left nb
      exact Or.inl ⟨Bool.eq_false_iff.mpr (fun h => hnl ⟨h,lb⟩), Bool.eq_false_iff.mpr nb⟩
    · have nb : Lval b ≠ true := fun h => hnl ⟨haL,h⟩
      have pb := hcb.resolve_right nb
      exact Or.inr ⟨Bool.eq_false_iff.mpr (fun h => hnp ⟨h,pb⟩), Bool.eq_false_iff.mpr nb⟩
