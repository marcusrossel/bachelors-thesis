import network.graph
import network.precedence

open network

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

  def eq_except_r (n n' : network) (i : reactor.id) : Prop :=
    n ≈ n' ∧ ∀ x ≠ i, n.η.data x = n'.η.data x

  def eq_except_o (n n' : network) (i : port.id) : Prop :=
    let r := i.rtr in n.eq_except_r n' r ∧ (n.η.data r).eq_except (n'.η.data r) i.prt

  noncomputable def edges_out_of (n : network) (p : port.id) : finset {e // e ∈ n} :=
    n.η.edges.attach.filter (λ e, (e : graph.edge).src = p)

  noncomputable def update_reactor (n : network) (i : reactor.id) (r : reactor) (h : n.η.data i ≈ r) : network :=
    {
      η := n.η.update_data i r,
      unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_with_equiv_rtr_is_equiv _ _ _ h) n.prec_acyclic
    }

  noncomputable def update_input (n : network) (p : port.id) (v : option value) : network :=
    update_reactor n p.rtr ((n.η.data p.rtr).update_input p.prt v) (reactor.update_input_equiv _ _ _)

  lemma edge_mem_equiv_trans {n n' : network} {e : graph.edge} :
    n' ≈ n → e ∈ n → e ∈ n' :=
    begin
      intros hₑ hₘ,
      simp [(≈)] at hₑ,
      simp [(∈)],
      rw hₑ.left,
      apply hₘ
    end

  lemma update_reactor_equiv (n : network) (i : reactor.id) (r : reactor) (h : n.η.data i ≈ r) :
    (n.update_reactor i r h) ≈ n :=
    begin
      unfold update_reactor,
      exact symm (graph.update_with_equiv_rtr_is_equiv n.η i r h)
    end

  lemma update_input_equiv (n : network) (p : port.id) (v : option value) :
    (n.update_input p v) ≈ n :=
    begin
      unfold update_input,
      simp [(≈)],
      apply update_reactor_equiv
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

end network