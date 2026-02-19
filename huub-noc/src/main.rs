pub(crate) mod game;
mod no_opponent_cycle;

use huub::{
	lower::InitConfig,
	model::{Model, expressions::BoolFormula},
	solver::{BoolValuation, Solver},
};
use no_opponent_cycle::NoOpponentCycle;
use pindakaas::solver::cadical::Cadical;

use pindakaas::propositional_logic::Formula;

pub(crate) use crate::game::Game;

fn main() {
	// -- Suggested workflow --
	// 1. Read a new Game object (file should be provided as command-line argument).
	// let game: Game = todo!();
	let game = Game::new(
		vec![0, 1, 0],          // owners (unused by current NOCQ parity-only)
		vec![1, 2, 4],          // priors
		vec![0, 1, 2],          // sources
		vec![1, 2, 0],          // targets
		vec![0, 0, 0],          // weights
		0,                      // init
		game::RewardType::Min,  // reward (unused by current NOCQ)
	);

	// 2. Construct a new huub::model::Model, add clausal constraint and
	//    Constraint/Propagator.
	let mut prb = Model::default();
	let edges: Vec<_> = (0..game.num_edges())
		.map(|_| prb.new_bool_decision())
		.collect();

	let vertices: Vec<_> = (0..game.num_vertices())
		.map(|_| prb.new_bool_decision())
		.collect();

	// make init vertex active
	prb.proposition(Formula::Atom(vertices[game.init])).post();

	// force a partial path 0->1, 1->2 and 2->0
	prb.proposition(Formula::Atom(edges[0])).post();
	prb.proposition(Formula::Atom(edges[1])).post();
	prb.proposition(Formula::Atom(edges[2])).post();

	prb.post_constraint(NoOpponentCycle {
		vertices: vertices.clone(),
		edges: edges.clone(),
		game: game.clone(),
	});

	// 3. Transform into huub::solver::Solver and solve problem.
	let Ok((mut slv, map)): Result<(Solver<Cadical>, _), _> = prb.to_solver(&InitConfig::default())
	else {
		println!("UNSATISFIABLE!");
		return;
	};
	let vertices: Vec<_> = vertices.into_iter().map(|v| map.get(&mut slv, v)).collect();
	let edges: Vec<_> = edges.into_iter().map(|e| map.get(&mut slv, e)).collect();
	let mut solution: Option<(Vec<bool>, Vec<bool>)> = None;
	slv.solve(|sol| {
		solution = Some((
			vertices.iter().map(|v| v.val(sol)).collect(),
			edges.iter().map(|e| e.val(sol)).collect(),
		))
	});

	// 4. Check correctness of solution.
	if let Some((vertices, edges)) = solution {
		println!("SATISFIABLE!");
		println!("Vertices: {:?}", vertices);
		println!("Edges: {:?}", edges);
		// JD Note: We need to know that the solution is correct, so you better
		// check it!
		check_solution(&game, &edges);
	} else {
		println!("UNSATISFIABLE!");
	}
}

// Check function
fn check_solution(game: &Game, edge_vals: &[bool]) {
    // state: 0=unvisited, 1=visiting(on recursion stack), 2=done
    let n = game.num_vertices();
    let mut state = vec![0u8; n];
    let mut parent_edge: Vec<Option<usize>> = vec![None; n];
    let mut parent_v: Vec<Option<usize>> = vec![None; n];

    fn dfs(
        game: &Game,
        edge_vals: &[bool],
        v: usize,
        state: &mut [u8],
        parent_edge: &mut [Option<usize>],
        parent_v: &mut [Option<usize>],
    ) -> Option<Vec<usize>> {
        state[v] = 1;

        for &e in game.out_edges(v) {
            if !edge_vals[e] { continue; }
            let u = game.target(e);

            if state[u] == 0 {
                parent_edge[u] = Some(e);
                parent_v[u] = Some(v);
                if let Some(cyc) = dfs(game, edge_vals, u, state, parent_edge, parent_v) {
                    return Some(cyc);
                }
            } else if state[u] == 1 {
                // found back edge v->u, reconstruct cycle edges
                let mut cyc = vec![e];
                let mut cur = v;
                while cur != u {
                    let pe = parent_edge[cur].expect("missing parent edge");
                    cyc.push(pe);
                    cur = parent_v[cur].expect("missing parent v");
                }
                cyc.reverse();
                return Some(cyc);
            }
        }

        state[v] = 2;
        None
    }

    let mut found: Option<Vec<usize>> = None;
    for v in 0..n {
        if state[v] == 0 {
            if let Some(cyc) = dfs(game, edge_vals, v, &mut state, &mut parent_edge, &mut parent_v) {
                found = Some(cyc);
                break;
            }
        }
    }

    match found {
        None => println!("No cycle detected."),
        Some(cycle_edges) => {
            println!("Cycle detected! edges = {:?}", cycle_edges);

            // also compute max priority parity on the cycle (same rule as your current NOCQ)
            let mut maxp: i64 = i64::MIN;
            for &e in &cycle_edges {
                let s = game.source(e);
                let t = game.target(e);
                maxp = maxp.max(game.prior(s));
                maxp = maxp.max(game.prior(t));
            }
            println!("cycle max priority = {}, parity = {}", maxp, (maxp & 1));
        }
    }
}
