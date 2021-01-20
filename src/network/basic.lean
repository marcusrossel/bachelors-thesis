import network.graph
import network.precedence

open network

@[ext]
structure network :=
  (η : network.graph)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.

namespace network

  @[reducible]
  instance mem : has_mem graph.edge network := {mem := λ e n, e ∈ n.η.edges}

  instance equiv : has_equiv network := ⟨λ n n', n.η ≈ n'.η⟩

  instance : is_equiv network (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  lemma edge_mem_equiv_trans {n n' : network} {e : graph.edge} :
    n' ≈ n → e ∈ n → e ∈ n' :=
    begin
      intros hₑ hₘ,
      simp [(≈)] at hₑ,
      simp [(∈)],
      rw hₑ.left,
      apply hₘ
    end

  -- The output port in a network graph, that is associated with a given port ID.
  noncomputable def output (n : network) (p : port.id) : option value :=
    option.join ((n.η.data p.rtr).output.nth p.prt)

  noncomputable def edges_out_of (n : network) (p : port.id) : finset graph.edge :=
    n.η.edges.filter (λ e, (e : graph.edge).src = p)

  noncomputable def dₒ (n : network) (i : reaction.id) : finset port.id :=
    (n.η.rcn i).dₒ.image (λ p, {port.id . rtr := i.rtr, prt := p})

  noncomputable def update_reactor (n : network) (i : reactor.id) (r : reactor) (h : n.η.data i ≈ r) : network :=
    {
      η := n.η.update_data i r,
      unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_with_equiv_rtr_is_equiv _ _ _ h) n.prec_acyclic
    }

  noncomputable def update_input (n : network) (p : port.id) (v : option value) : network :=
    update_reactor n p.rtr ((n.η.data p.rtr).update_input p.prt v) (reactor.update_input_equiv _ _ _)

  lemma update_reactor_equiv (n : network) (i : reactor.id) (r : reactor) (h : n.η.rtr i ≈ r) :
      (n.update_reactor i r h) ≈ n :=
      begin
        unfold update_reactor,
        exact symm_of (≈) (graph.update_with_equiv_rtr_is_equiv n.η i r h)
      end

  lemma update_input_equiv (n : network) (p : port.id) (v : option value) :
    (n.update_input p v) ≈ n :=
    begin
      unfold update_input,
      simp [(≈)],
      apply update_reactor_equiv
    end

  lemma update_reactor_out_inv (n : network) (i : reactor.id) (rtr : reactor) (hₑ : n.η.rtr i ≈ rtr) (h : rtr.output = (n.η.rtr i).output) :
    ∀ o, (n.update_reactor i rtr hₑ).output o = n.output o :=
    begin
      intro o,
      unfold output,
      suffices h : ((n.update_reactor i rtr hₑ).η.data o.rtr).output = (n.η.data o.rtr).output, { rw h },
      unfold update_reactor digraph.update_data,
      simp,
      rw function.update_apply,
      by_cases hᵢ : o.rtr = i,
        {
          rw [if_pos hᵢ, hᵢ],
          exact h
        },
        rw if_neg hᵢ
    end

  lemma update_input_out_inv (n : network) (p : port.id) (v : option value) :
    ∀ o, (n.update_input p v).output o = n.output o :=
    begin
      unfold update_input,
      apply update_reactor_out_inv,
      apply reactor.update_input_out_inv
    end

  lemma update_reactor_comm {i i' : reactor.id} (h : i ≠ i') (r r' : reactor) (n : network) :
    ∀ hₗ hₗ' hᵣ' hᵣ, (n.update_reactor i r hₗ).update_reactor i' r' hₗ' = (n.update_reactor i' r' hᵣ').update_reactor i r hᵣ :=
    begin
      intros hₗ hₗ' hᵣ' hᵣ,
      unfold update_reactor,
      simp,
      apply digraph.update_data_comm,
      exact h,
    end 

  lemma update_input_comm {i i' : port.id} (h : i ≠ i') (v v' : option value) (n : network) :
    (n.update_input i v).update_input i' v' = (n.update_input i' v').update_input i v :=
    begin
      unfold update_input,
      by_cases hᵣ : i.rtr = i'.rtr
        ; sorry
    end

end network