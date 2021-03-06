import topo
import inst.network.basic 

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

namespace inst
namespace network

  -- A function that can generate a well-formed precedence graph for a given instantaneous network.
  @[ext]
  structure prec_func :=
    (func : inst.network υ → prec.graph υ)
    (well_formed : ∀ σ, func σ ⋈ σ.η)

  -- A function that can generate a complete topological ordering for a given precedence graph.
  structure topo_func :=
    (func : prec.graph υ → list reaction.id)
    (is_topo : ∀ {σ : inst.network υ} {ρ : prec.graph υ}, (func ρ).is_complete_topo_over ρ)

  variable {υ}

  -- Calling an instance of `prec_func` as a function, means calling its `func`.
  instance prec_func_coe : has_coe_to_fun (prec_func υ) := ⟨_, (λ f, f.func)⟩

  -- Calling an instance of `topo_func` as a function, means calling its `func`.
  instance topo_func_coe : has_coe_to_fun (topo_func υ) := ⟨_, (λ f, f.func)⟩

  -- The precedence function is unique.
  theorem prec_func.unique (p p' : prec_func υ) : p = p' :=
    begin
      rw prec_func.ext p p',
      funext σ,
      exact prec.wf_prec_graphs_are_eq (p.well_formed σ) (p'.well_formed σ)
    end

end network
end inst
