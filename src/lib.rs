/*
============================================================
NOCQ – No Opponent Cycle (Parity Game toy propagator)

This file is a minimal Rust practice version of a parity-game
cycle detector propagator.

Goal:
- Detect cycles in a directed graph.
- Compute the maximum priority on the cycle.
- If the maximum priority is ODD:
    -> disable the closing edge (set_bool(false)).
- If EVEN:
    -> do nothing.

This is NOT connected to Huub yet.
It is a standalone structural and recursion practice version.

Key simplifications:
- BoolView is just an index wrapper.
- Reason = Vec<BoolView> (no sign stored).
- MiniActions is a fake assignment store for testing.
- ExplanationActions is implemented for () (unit type).
============================================================
*/

// ------------------------------------------------------------
// Basic SAT-like abstractions (minimal practice version)
// ------------------------------------------------------------

// BoolView represents a boolean variable by its index.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolView(pub usize);

#[derive(Debug, Clone)]
pub struct Conflict {
    pub var: BoolView,
    pub existing: bool,
    pub requested: bool,
}
pub type Reason = Vec<BoolView>;

// ------------------------------------------------------------
// Solver interaction traits
// ------------------------------------------------------------
pub trait PropagationActions {
    fn attach(&mut self, _v: BoolView) {}
    /// Assign variable with explanation.
    /// Returns:
    /// - Ok(())     if assignment succeeds or is redundant
    /// - Err(...)   if assignment contradicts existing value
    fn value(&mut self, v: BoolView) -> Result<Option<bool>, Conflict>;
    /// Assign variable with explanation.
    fn set_bool(&mut self, v: BoolView, val: bool, reason: Reason) -> Result<(), Conflict>;
}

pub trait ExplanationActions {
    fn new_explanation(&mut self) -> Reason;
    /// In real solver: would add literal with polarity.
    /// Here: only stores BoolView.
    fn add_literal(&mut self, reason: &mut Reason, v: BoolView, val: bool);
}

// ------------------------------------------------------------
// Parity game structure
// ------------------------------------------------------------
//
// priority[v] = priority of vertex v
// outs[v]     = list of outgoing edge indices
// targets[e]  = target vertex of edge e

struct GAME {
    priority: Vec<u32>,
    outs: Vec<Vec<usize>>,
    targets: Vec<usize>,
}

impl GAME {
    fn priority(&self, v: usize) -> u32 {
        self.priority[v]
    }

    fn get_outs(&self, v:usize) -> &[usize] {
        &self.outs[v]
    }

    fn target(&self, e:usize) -> usize{
        self.targets[e]
    }

    fn nvertices(&self) -> usize{
        self.outs.len()
    }
}

// ------------------------------------------------------------
// NOCQ Propagator
// ------------------------------------------------------------
//
// E: edge variables
// V: vertex variables (not heavily used in this toy model)
// game: underlying parity game graph

struct NOCQ {
    E: Vec<BoolView>,
    V: Vec<BoolView>,
    game: GAME,
}

impl NOCQ {
    pub fn new(
        E: Vec<BoolView>,
        V: Vec<BoolView>,
        game: GAME,
    ) -> Self {
        Self { E, V, game }
    }

    /*
    ------------------------------------------------------------
    noceager – recursive cycle exploration

    Parameters:
    - path_v: current vertex path
    - path_e: current edge path
    - v:      current vertex
    - e:      incoming edge
    - defined: whether current edge is true

    Logic:

    1) If current vertex v already appears in path_v:
         -> we found a cycle.
         -> compute maximum priority on cycle.
         -> if max priority is ODD:
                disable closing edge (set_bool(false)).
         -> return.

    2) If current edge is defined true:
         -> explore outgoing edges recursively.

    This mirrors parity-game cycle detection logic.
    ------------------------------------------------------------
    */
    fn noceager<P, Expl>(
        &self,
        actions: &mut P,
        expl: &mut Expl,
        path_v: &mut Vec<usize>,
        path_e: &mut Vec<usize>,
        v: usize,
        e: usize,
        defined: bool,
    ) -> Result<(), Conflict> 
    where 
        P: PropagationActions,
        Expl: ExplanationActions,
    {
        // if v ∈ path_V then
        if let Some(i_v) = path_v.iter().position(|&x| x == v) {
            // i_v <- index(v, path_V)

            // m <- max{ priority(v') | v' ∈ path_V[i_v:] }
            let mut m: u32 = 0;
            for &vv in &path_v[i_v..] {
                let pr = self.game.priority(vv);
                if pr > m {
                    m = pr;
                }
            }
            // if m mod 2 = p
            let odd = (m % 2) == 1;

            if odd {
                let mut reason = expl.new_explanation();
                for &e_prime in &path_e[i_v..] {
                    expl.add_literal(&mut reason, self.E[e_prime], false);
                }
                actions.set_bool(self.E[e], false, reason)?;
            }

            return Ok(());
        }

        // if defined
        if defined {
            // for e' ∈ edges(v) where 𝓔[e'] ≠ ⊥ do
            for &e2 in self.game.get_outs(v) {
                let val = actions.value(self.E[e2])?;

                // 𝓔[e2] == ⊥(false) -> skip
                if val == Some(false){
                    continue;
                }

                // p_V <- path_V ∪ {v}
                path_v.push(v);
                // p_E <- path_E ∪ {e'}
                path_e.push(e2);

                // w <- target(e')
                let w = self.game.target(e2);
                // def <- 𝓔[e'] = ⊤
                let def = val ==Some(true);
                // NOCEager(p_V, p_E, w, e', 𝓔, def)
                self.noceager(
                    actions,
                    expl,
                    path_v,
                    path_e,
                    w,
                    e2,
                    def,
                )?;

                path_v.pop();
                path_e.pop();
            }
        }
        // return ⊤
        Ok(())
    }
}

// ------------------------------------------------------------
// Generic Propagator interface
// ------------------------------------------------------------
pub trait Propagator<P, Expl> {
    fn initialize(&mut self, actions: &mut P) -> Result<(), Conflict>;
    fn propagate(&mut self, actions: &mut P, expl: &mut Expl) -> Result<(), Conflict>;
}

impl<P, Expl> Propagator<P, Expl> for NOCQ 
where
    P: PropagationActions,
    Expl: ExplanationActions,
{
    fn initialize(&mut self, actions: &mut P) -> Result<(), Conflict> {
        for v in &self.V {
            actions.attach(*v);
        }
        for e in &self.E {
            actions.attach(*e);
        }
        Ok(())
    }

    /*
    ------------------------------------------------------------
    propagate:

    For every vertex:
        For every outgoing edge:
            If edge is defined (true or false):
                start recursive cycle detection.

    If a cycle with odd maximum priority is found:
        -> disable the closing edge.

    This is a brute-force exploration version.
    ------------------------------------------------------------
    */
    fn propagate(&mut self, actions: &mut P, expl: &mut Expl) -> Result<(), Conflict> {
        let n = self.game.nvertices();

        for v in 0..n {
            let mut path_v: Vec<usize> = Vec::new();
            let mut path_e: Vec<usize> = Vec::new();

            for &e in self.game.get_outs(v) {
                let val = actions.value(self.E[e])?;
                if val.is_none(){
                    continue;
                }
                // defined = (𝓔[e] == ⊤)
                let def = val == Some(true);
                // Call NOCEager with current root vertex v and outgoing edge e.
                self.noceager(actions, expl, &mut path_v, &mut path_e, v, e, def)?;
            }
        }

        Ok(())
    }
}

// ------------------------------------------------------------
// Minimal explanation implementation for unit type.
// Used only for testing.
// ------------------------------------------------------------
impl ExplanationActions for () {
    fn new_explanation(&mut self) -> Reason { Vec::new() }
    fn add_literal(&mut self, reason: &mut Reason, v: BoolView, _val: bool) {
        reason.push(v);
    }
}

// ------------------------------------------------------------
// MiniActions
//
// Fake solver state used only for testing.
// Stores Option<bool> for each edge variable.
//
// This replaces real SAT engine interaction.
// ------------------------------------------------------------
struct MiniActions {
    vals: Vec<Option<bool>>,
}

impl MiniActions {
    fn new(n: usize) -> Self { Self { vals: vec![None; n] } }
}

impl PropagationActions for MiniActions {
    fn value(&mut self, v: BoolView) -> Result<Option<bool>, Conflict> {
        Ok(self.vals[v.0])
    }
    fn set_bool(&mut self, v: BoolView, val: bool, _reason: Reason)
        -> Result<(), Conflict>
    {
        match self.vals[v.0] {
            None => {
                self.vals[v.0] = Some(val);
                Ok(())
            }
            Some(existing) if existing == val => {
                Ok(())
            }
            Some(existing) => {
                Err(Conflict {
                    var: v,
                    existing,
                    requested: val,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /*
    Parity game graph used for testing.

    Graph structure (directed):

                 (0)
                /   \
               v     v
              (1)   (4)
               |     |
               v     v
              (2)   (5)
               |     |
               v     v
              (3)   (6)
              / \    / \
             v   v  v   v
            (1) (7)(4) (0)
                 |
                 v
                (2)

    -------------------------------------------
    Odd cycle:
        1 → 2 → 3 → 1
        max priority = 5 (odd)

    Even cycle:
        4 → 5 → 6 → 4
        max priority = 8 (even)
    -------------------------------------------
    */
    fn build_test_game() -> GAME {
        GAME {
            // index = vertex id
            priority: vec![
                0,  // 0
                2,  // 1
                5,  // 2  <-- highest in odd cycle
                4,  // 3
                6,  // 4
                2,  // 5
                8,  // 6  <-- highest in even cycle
                1,  // 7
            ],

            // outs[v] = list of outgoing edge ids
            outs: vec![
                vec![0, 1],     // 0 → 1, 4
                vec![2],        // 1 → 2
                vec![3],        // 2 → 3
                vec![4, 8],     // 3 → 1, 7
                vec![5],        // 4 → 5
                vec![6],        // 5 → 6
                vec![7, 10],    // 6 → 4, 0
                vec![9],        // 7 → 2
            ],

            // target[e] = destination vertex
            targets: vec![
                1,  // e0: 0 → 1
                4,  // e1: 0 → 4
                2,  // e2: 1 → 2
                3,  // e3: 2 → 3
                1,  // e4: 3 → 1  (odd cycle close)
                5,  // e5: 4 → 5
                6,  // e6: 5 → 6
                4,  // e7: 6 → 4  (even cycle close)
                7,  // e8: 3 → 7
                2,  // e9: 7 → 2
                0,  // e10: 6 → 0
            ],
        }
    }

    #[test]
    fn test_game_structure() {
        let g = build_test_game();

        assert_eq!(g.nvertices(), 8);

        // Check odd cycle max priority
        let odd_cycle = vec![1, 2, 3];
        let mut max = 0;
        for v in odd_cycle {
            max = max.max(g.priority(v));
        }
        assert_eq!(max % 2, 1); // should be odd

        // Check even cycle max priority
        let even_cycle = vec![4, 5, 6];
        let mut max2 = 0;
        for v in even_cycle {
            max2 = max2.max(g.priority(v));
        }
        assert_eq!(max2 % 2, 0); // should be even
    }

    #[test]
    // All edges start as true.
    // Odd cycle should disable edge e4 (3 -> 1).
    fn test_nocq_propagate_sets_edge_false_on_odd_cycle() {
        let game = build_test_game();

        let nedges = game.targets.len();
        let nverts = game.nvertices();

        let e: Vec<BoolView> = (0..nedges).map(BoolView).collect();
        let v: Vec<BoolView> = (0..nverts).map(BoolView).collect();

        let mut nocq = NOCQ::new(e, v, game);

        // Only set the path edges of the odd cycle to true.
        // Leave the closing edge (e4: 3->1) as None so the propagator can set it to false.
        let mut actions = MiniActions::new(nedges);
        actions.vals[2] = Some(true); // e2: 1 -> 2
        actions.vals[3] = Some(true); // e3: 2 -> 3
        actions.vals[4] = None;       // e4: 3 -> 1 (closing edge)

        let mut expl = ();

        nocq.propagate(&mut actions, &mut expl).unwrap();

        // odd cycle back-edge is e4 (3->1). Your noceager sets it to false.
        assert_eq!(actions.vals[4], Some(false));
    }

    #[test]
    // Even cycle should NOT disable edge e7 (6 -> 4).
    fn test_nocq_does_not_disable_edge_on_even_cycle() {
        let game = build_test_game();

        let nedges = game.targets.len();
        let nverts = game.nvertices();

        let e: Vec<BoolView> = (0..nedges).map(BoolView).collect();
        let v: Vec<BoolView> = (0..nverts).map(BoolView).collect();

        let mut nocq = NOCQ::new(e, v, game);

        // Only set the even cycle edges to true:
        // 4 -> 5 (e5), 5 -> 6 (e6), 6 -> 4 (e7).
        // Leave everything else as None to avoid triggering odd-cycle constraints.
        let mut actions = MiniActions::new(nedges);
        actions.vals[5] = Some(true); // e5: 4 -> 5
        actions.vals[6] = Some(true); // e6: 5 -> 6
        actions.vals[7] = Some(true); // e7: 6 -> 4 (even cycle close)

        let mut expl = ();

        // run propagate (should not fail in this toy setup)
        nocq.propagate(&mut actions, &mut expl).unwrap();

        // even cycle back-edge is e7 (6->4), should remain true
        assert_eq!(actions.vals[7], Some(true));
    }

    #[test]
    fn test_nocq_conflict_when_edge_already_true() {
        let game = build_test_game();
        let nedges = game.targets.len();
        let nverts = game.nvertices();

        let e: Vec<BoolView> = (0..nedges).map(BoolView).collect();
        let v: Vec<BoolView> = (0..nverts).map(BoolView).collect();
        let mut nocq = NOCQ::new(e, v, game);

        let mut actions = MiniActions::new(nedges);

        // Only enable the odd-cycle path so the propagator reaches the cycle:
        // 1 -> 2 (e2), 2 -> 3 (e3), 3 -> 1 (e4).
        actions.vals[2] = Some(true); // e2: 1 -> 2
        actions.vals[3] = Some(true); // e3: 2 -> 3

        // Force the closing odd-cycle edge e4 to already be true.
        // Propagator will try to set it false -> conflict.
        actions.vals[4] = Some(true); // e4: 3 -> 1

        let mut expl = ();

        let res = nocq.propagate(&mut actions, &mut expl);
        assert!(res.is_err());
    }
}