import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  noncomputable def propagate_edge (σ : network) : {n // n ≈ σ} → {e // e ∈ σ} → {n // n ≈ σ} := λ n e,
    {
      val := (n : network).update_input (e : graph.edge).dst (σ.output (e : graph.edge).src),
      property := trans_of (≈) (update_input_equiv n _ _) (n.property)
    }

  lemma prop_edge_comm (σ : network) : 
    right_commutative (propagate_edge σ) :=
    begin
      unfold right_commutative,
      intros n e e',
      by_cases (e : graph.edge) = ↑e',
        rw (subtype.eq h),
        {
          have hₑ  : ↑e  ∈ (n : network), from edge_mem_equiv_trans n.property e.property,
          have hₑ' : ↑e' ∈ (n : network), from edge_mem_equiv_trans n.property e'.property,
          have hᵤ, from (n : network).unique_ins,
          rw graph.has_unique_port_ins at hᵤ,
          replace h : ↑e ≠ ↑e' := by exact h,
          have h_d : (e : graph.edge).dst ≠ (e' : graph.edge).dst, from hᵤ _ _ hₑ hₑ' h,
          unfold propagate_edge,
          simp,
          exact update_input_comm h_d _ _ ↑n
        }
    end

  lemma propagate_edge_equiv (σ : network) :
    ∀ n e, ↑(σ.propagate_edge n e) ≈ (n : network) :=
    begin
      unfold propagate_edge,
      apply graph.update_input_equiv
    end

  lemma propagate_edge_out_inv (σ : network) (η : network.graph) (e : graph.edge) :
    ∀ n e o, (σ.propagate_edge n e : network).output o = (n : network).output o :=
    begin
      intro o,
      unfold propagate_edge,
      apply graph.update_input_out_inv
    end

  private noncomputable def propagate_edges : network → list graph.edge → network :=
    list.foldl propagate_edge

  lemma propagate_edges_equiv (η : network.graph) (e : list network.graph.edge) :
    propagate_edges η e ≈ η :=
    begin
      induction e generalizing η,
        case list.nil {
          simp only [(≈)],
          finish 
        },
        case list.cons : eₕ eₜ hᵢ {
          unfold propagate_edges,
          have h, from propagate_edge_equiv η eₕ,
          have h', from hᵢ (propagate_edge η eₕ),
          exact trans_of (≈) h' h
        } 
    end

  lemma propagate_edges_order_indep (η : network.graph) (e e' : list network.graph.edge) (hᵤ : η.has_unique_port_ins) (hₚ : e' ~ e) (hₘ : ∀ x ∈ e, x ∈ η) :
    propagate_edges η e = propagate_edges η e' :=
    begin
      unfold propagate_edges,
      rw list.perm.foldl_eq sorry hₚ η 
    end

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  private noncomputable def propagate_port (η : network.graph) (p : port.id) : network.graph := 
    propagate_edges η (η.edges_out_of p).val.to_list 

  lemma propagate_port_equiv (η : network.graph) (p : port.id) :
    propagate_port η p ≈ η :=
    begin
      unfold propagate_port,
      induction (η.edges_out_of p).val.to_list
        ; apply propagate_edges_equiv
    end

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_ports : network.graph → list port.id → network.graph :=
    list.foldl propagate_port

  lemma propagate_ports_order_indep (η : network.graph) (p p' : list port.id) (hᵤ : η.has_unique_port_ins) (hₚ : p' ~ p) :
    propagate_ports η p = propagate_ports η p' :=
    begin
      unfold propagate_ports,
      rw list.perm.foldl_eq' sorry hₚ η
    end

  lemma propagate_ports_equiv (η η' : network.graph) (p : list port.id) (h : η ≈ η') :
    propagate_ports η p ≈ η' :=
    begin
      induction p with pₕ pₜ hᵢ generalizing η,
        case list.nil {
          unfold propagate_ports,
          exact h
        },
        case list.cons {
          unfold propagate_ports,
          have hₑ, from propagate_port_equiv η pₕ,
          have hₑ', from trans_of (≈) hₑ h,
          have hᵢ', from hᵢ (propagate_port η pₕ),
          exact hᵢ' hₑ'
        }
    end

  private noncomputable def propagate_output (η : network.graph) (i : reaction.id) : network.graph :=
    propagate_ports η (η.dₒ i).val.to_list 

  lemma propagate_output_equiv (η η' : network.graph) (i : reaction.id) (h : η ≈ η') :
    propagate_output η i ≈ η' :=
    begin
      unfold propagate_output,
      induction (η.dₒ i).val.to_list
        ; apply propagate_ports_equiv
        ; exact h
    end

  private noncomputable def run_reaction (η : network.graph) (i : reaction.id) : network.graph :=
    propagate_output (η.update_reactor i.rtr ((η.rtr i.rtr).run i.rcn) (reactor.run_equiv _ _)) i
      
  lemma run_reaction_equiv (η : network.graph) (i : reaction.id) :
    run_reaction η i ≈ η :=
    begin
      unfold run_reaction,
      apply propagate_output_equiv,
      apply graph.update_reactor_equiv
    end

  private noncomputable def run_topo : network.graph → list reaction.id → network.graph
    | η [] := η
    | η (topoₕ :: topoₜ) := run_topo (run_reaction η topoₕ) topoₜ

  lemma run_topo_equiv (η : network.graph) (t : list reaction.id) :
    run_topo η t ≈ η :=
    begin
      induction t with tₕ tₜ hᵢ generalizing η,
        case list.nil {
          unfold run_topo,
          exact refl_of (≈) η
        },
        case list.cons {
          unfold run_topo,
          have hₑ, from run_reaction_equiv η tₕ,
          have hᵢ', from hᵢ (run_reaction η tₕ),
          exact trans_of (≈) hᵢ' hₑ
        }
    end

  lemma run_topo_unique_ports_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).has_unique_port_ins :=
    begin
      have h, from run_topo_equiv n.η topo,
      exact network.graph.edges_inv_unique_port_ins_inv (symm h).left n.unique_ins
    end 
    
  lemma run_topo_prec_acyc_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).is_prec_acyclic :=
    begin
      have h, from run_topo_equiv n.η topo,
      exact network.graph.equiv_prec_acyc_inv (symm h) n.prec_acyclic
    end 

  theorem run_topo_indep (η : network.graph) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over η) :
    ∀ (t t') (h_t : ρ.topological_order h_a t) (h_t' : ρ.topological_order h_a t'), run_topo η t = run_topo η t' :=
    begin
      sorry
    end

  private noncomputable def run_aux (n : network) (t : list reaction.id) : network :=
    {η := run_topo n.η t, unique_ins := run_topo_unique_ports_inv n t, prec_acyclic := run_topo_prec_acyc_inv n t}

  noncomputable def run (n : network) (fₚ : prec_func) (fₜ : topo_func) : network :=
    run_aux n (fₜ (fₚ n))

  theorem run_equiv (n : network) (fₚ : prec_func) (fₜ : topo_func) :
    (n.run fₚ fₜ).η ≈ n.η :=
    begin
      unfold run run_aux,
      simp,
      apply run_topo_equiv
    end

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq p p',
      unfold run run_aux,
      suffices h : run_topo n.η (t (p' n)) = run_topo n.η (t' (p' n)), {
        ext1,
        simp,
        exact h
      },
      have h_pnw : (p' n).is_well_formed_over n.η, from p'.well_formed n,
      have h_pna : (p' n).is_acyclic, from n.prec_acyclic (p' n) h_pnw,
      have h_t   : (p' n).topological_order h_pna (t (p' n)), from t.is_topo _ _ h_pnw,
      have h_t'  : (p' n).topological_order h_pna (t' (p' n)), from t'.is_topo _ _ h_pnw,
      exact run_topo_indep n.η _ h_pna h_pnw _ _ h_t h_t'
    end

end network