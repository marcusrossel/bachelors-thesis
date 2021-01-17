import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  def is_edge_propagated (n' n : network) (e : graph.edge) : Prop :=
    n'.eq_except_o n e.dst ∧ n'.η.input e.dst = n.η.input e.src

  def is_port_propagated (n' n : network) (p : port.id) : Prop :=
    ∀ e ∈ (n.edges_out_of p), n'.is_edge_propagated n ↑e /-- ∧ n'.eq_except_os n (n.edges_out_of p) --/ 

  def is_output_propagated (n' n : network) (o : finset port.id) : Prop :=
    ∀ p ∈ o, n'.is_port_propagated n p

  -- `n'` is the result of processing reaction `i` iff 
  -- there is some network `nₘ` where the reactor for `i` has run that reaction and
  -- `n'` is a version of `nₘ` where the corresponding output ports have been propagated
  def is_reaction_processed (n' n : network) (i : reaction.id) : Prop :=
    ∃ nₘ : network, 
      nₘ.eq_except_r n i.rtr ∧ 
      nₘ.η.rtr i.rtr = (n.η.rtr i.rtr).run i.rcn ∧
      n'.is_output_propagated nₘ (nₘ.η.dₒ i)

  -- Case 1 : `n'` is the result of running `n` over an empty topo list iff `n = n'`
  -- Case 2 : `n'` is the result of running `n` over a topo list `(h :: t)` iff 
  --          the result of running `h` on `n` is called `nₘ` and `n'` is the result of running `t`
  --          over *that* (over `nₘ`)
  def is_topo_processed : network → network → list reaction.id → Prop 
    | n' n [] := (n = n')
    | n' n (h :: t) := ∃ nₘ : network, nₘ.is_reaction_processed n h ∧ n'.is_topo_processed nₘ t
 
  -- The `n ≈ n'` is required to solve part of the frame problem. That is, it ensures that the
  -- structure of the network remains the same. So `is_topo_processed` only has to make sure that
  -- *all* port and state values make sense.
  def is_processed (n' n : network) (prec_func : prec_func) (topo_func : topo_func) : Prop :=
    n'.is_topo_processed n (topo_func (prec_func n))

  theorem any_net_has_processed_net (n : network) (p : prec_func) (t : topo_func) :
    ∃ n' : network, n'.is_processed n p t :=
    sorry

  theorem any_net_has_exactly_one_processed_net (n : network) (p : prec_func) (t : topo_func) :
    ∃! nₚ : network, nₚ.is_processed n p t := 
    begin
      unfold exists_unique,
      obtain ⟨nₚ, hₚ⟩ := classical.subtype_of_exists (any_net_has_processed_net n p t),
      existsi (nₚ : network),
      suffices h : ∀ (nₚ' : network), nₚ'.is_processed n p t → nₚ' = nₚ, from ⟨hₚ, h⟩,
      intros nₚ' hₚ',
      unfold is_processed at hₚ hₚ',
      sorry
    end

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    begin
      -- Use all_prec_funcs_are_eq p p',
    end

end network