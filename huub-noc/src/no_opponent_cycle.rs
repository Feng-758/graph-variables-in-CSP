use huub::{
	actions::{PostingActions, ReasoningEngine},
	constraints::{
		BoolModelActions, BoolSolverActions, Constraint, Propagator, SimplificationStatus,
	},
	lower::{LoweringContext, LoweringError},
};

use crate::Game;

// JD Note: This contains all the data that the NoOpponentCycle
// constraint/propagator needs to function.
#[derive(Debug, Clone)]
pub(crate) struct NoOpponentCycle<BoolView> {
	pub(crate) vertices: Vec<BoolView>,
	pub(crate) edges: Vec<BoolView>,
	pub(crate) game: Game,
}

impl<B, E> Propagator<E> for NoOpponentCycle<B>
where
	B: BoolSolverActions<E>,
	E: ReasoningEngine,
{
	fn initialize(&mut self, ctx: &mut E::InitializationCtx<'_>) {
		for b in self.vertices.iter().chain(self.edges.iter()) {
			b.enqueue_when_fixed(ctx);
		}
	}

	fn propagate(&mut self, ctx: &mut E::PropagationCtx<'_>) -> Result<(), E::Conflict> {
		// todo!("JD Note: here is where you implement the propagation algorithm")
		let n = self.game.num_vertices();
		let m = self.game.num_edges();

		// cache current edge assignments: None/Some(true)/Some(false)
		let mut edge_val: Vec<Option<bool>> = vec![None; m];
		for e in 0..m {
			edge_val[e] = self.edges[e].val(ctx);
		}

		// NOCEager-style DFS state
		let mut path_v: Vec<usize> = Vec::new();
		let mut path_e: Vec<usize> = Vec::new();
		let mut in_stack: Vec<bool> = vec![false; n];

		// start DFS from every edge that is not fixed false
		for v in 0..n {
			for &e in self.game.out_edges(v) {
				if edge_val[e] == Some(false) {
					continue;
				}
				let w = self.game.target(e);
				let defined_true = edge_val[e] == Some(true);

				self.noceager_dfs(
					ctx,
					&edge_val,
					&mut path_v,
					&mut path_e,
					&mut in_stack,
					w,
					e,
					defined_true,
				)?;
			}
		}

		Ok(())
	}
}

impl<B> NoOpponentCycle<B> {
	// JD Note: here you can implement helper method for NoOpponentCycle that help
	// with `propagate`
	// -----------------------------
	// winner condition (Parity only)
	// -----------------------------
	//
	// Current:
	// - "opponent" is ODD
	// - forbid cycles whose max priority has odd parity
	
	fn cycle_is_forbidden_by_parity(&self, cycle_edges: &[usize]) -> bool {
		let mut maxp: i64 = i64::MIN;

		for &e in cycle_edges {
			let s = self.game.source(e);
			let t = self.game.target(e);
			maxp = maxp.max(self.game.prior(s));
			maxp = maxp.max(self.game.prior(t));
		}

		// odd max priority => opponent-winning => forbidden
		(maxp & 1) == 1
	}

	// ---------------------------------
	// NOCEager DFS
	// ---------------------------------
	fn noceager_dfs<E: ReasoningEngine>(
		&self,
		ctx: &mut E::PropagationCtx<'_>,
		edge_val: &[Option<bool>],
		path_v: &mut Vec<usize>,
		path_e: &mut Vec<usize>,
		in_stack: &mut [bool],
		v: usize,
		incoming_e: usize,
		defined_true: bool,
	) -> Result<(), E::Conflict>
	where
		B: BoolSolverActions<E>,
	{
		// case 1: found a cycle (back-edge to a vertex already on the stack)
		if in_stack[v] {
			let start = path_v
				.iter()
				.position(|&x| x == v)
				.expect("in_stack[v] implies v is on path_v");

			// cycle edges = edges along the stack segment + the closing edge incoming_e
			let mut cycle_edges: Vec<usize> = path_e[start..].to_vec();
			cycle_edges.push(incoming_e);

			if self.cycle_is_forbidden_by_parity(&cycle_edges) {
				// Reason: all edges on the stack segment must be true (by invariant),
				// i.e., path_e[start..] are true. Those imply we must cut the closing edge.
				let mut reason_atoms: Vec<E::Atom> = Vec::new();
				for &e in &path_e[start..] {
					// these are true edges that built the stack
					reason_atoms.push(self.edges[e].clone().into());
				}

				// Enforce incoming_e = false
				// - if incoming_e was already true, this will raise a conflict with the same reason
				self.edges[incoming_e].fix(ctx, false, reason_atoms)?;
			}

			return Ok(());
		}

		// case 2: only expand through edges that are already fixed true
		if defined_true {
			in_stack[v] = true;
			path_v.push(v);
			path_e.push(incoming_e);

			for &e2 in self.game.out_edges(v) {
				if edge_val[e2] == Some(false) {
					continue;
				}
				let w = self.game.target(e2);
				let def2 = edge_val[e2] == Some(true);

				self.noceager_dfs(ctx, edge_val, path_v, path_e, in_stack, w, e2, def2)?;
			}

			path_e.pop();
			path_v.pop();
			in_stack[v] = false;
		}

		Ok(())
	}
}

impl<B, E> Constraint<E> for NoOpponentCycle<B>
where
	E: ReasoningEngine,
	B: BoolModelActions<E>,
{
	fn simplify(
		&mut self,
		ctx: &mut E::PropagationCtx<'_>,
	) -> Result<SimplificationStatus, E::Conflict> {
		self.propagate(ctx)?;
		Ok(SimplificationStatus::NoFixpoint)
	}

	fn to_solver(&self, ctx: &mut LoweringContext<'_>) -> Result<(), LoweringError> {
		let vertices: Vec<_> = self
			.vertices
			.iter()
			.map(|v| ctx.solver_view(v.clone().into()))
			.collect();
		let edges: Vec<_> = self
			.edges
			.iter()
			.map(|v| ctx.solver_view(v.clone().into()))
			.collect();

		ctx.add_propagator(Box::new(NoOpponentCycle {
			vertices,
			edges,
			game: self.game.clone(),
		}));
		Ok(())
	}
}
