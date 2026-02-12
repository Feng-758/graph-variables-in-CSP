#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolView(pub usize);
pub struct Conflict;
pub type Reason = Vec<BoolView>;

pub trait PropagationActions {
    fn attach(&mut self, _v: BoolView) {}
    /// Read current value:
    /// - None  => unassigned (⊥)
    /// - Some(true/false) => assigned
    fn value(&mut self, v: BoolView) -> Result<Option<bool>, Conflict>;
    /// Assign a boolean with a reason (for explanation).
    fn set_bool(&mut self, v: BoolView, val: bool, reason: Reason) -> Result<(), Conflict>;
}

pub trait ExplanationActions {
    fn new_explanation(&mut self) -> Reason;
    fn add_literal(&mut self, reason: &mut Reason, v: BoolView, val: bool);
}

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
                // reason <- clausify(¬path_E[i_v:])
                let mut reason = Vec::new();
                for &e_prime in &path_e[i_v..] {
                    // add literal (E[e_prime] is false) == ¬E[e_prime]
                    reason.push(self.E[e_prime]);
                }
                
                // if not ( 𝓔[e] <- (⊥, reason) ) then return ⊥
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

impl ExplanationActions for () {
    fn new_explanation(&mut self) -> Reason { Vec::new() }
    fn add_literal(&mut self, reason: &mut Reason, v: BoolView, _val: bool) {
        reason.push(v);
    }
}

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
    fn set_bool(&mut self, v: BoolView, val: bool, _reason: Reason) -> Result<(), Conflict> {
        self.vals[v.0] = Some(val);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_test_game() -> GAME {

        /*
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
                (1)  (7)(4)  (0)
                      |
                      v
                     (2)

        ------------------------------------------------
        node info (player, priority):
        (0): player A, p=0
        (1): player B, p=2
        (2): player B, p=5   // odd-cycle max
        (3): player B, p=4
        (4): player A, p=6
        (5): player A, p=2
        (6): player A, p=8   // even-cycle max
        (7): player B, p=1
        */

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
    fn test_nocq_propagate_sets_edge_false_on_odd_cycle() {
        let game = build_test_game();

        let nedges = game.targets.len();
        let nverts = game.nvertices();

        let e: Vec<BoolView> = (0..nedges).map(BoolView).collect();
        let v: Vec<BoolView> = (0..nverts).map(BoolView).collect();

        let mut nocq = NOCQ::new(e, v, game);

        //make all edges defined true so recursion explores them
        let mut actions = MiniActions::new(nedges);
        for i in 0..nedges {
            actions.vals[i] = Some(true);
        }

        let mut expl = ();

        nocq.propagate(&mut actions, &mut expl);

        // odd cycle back-edge is e4 (3->1). Your noceager sets it to false.
        assert_eq!(actions.vals[4], Some(false));
    }

    #[test]
    fn test_nocq_does_not_disable_edge_on_even_cycle() {
        let game = build_test_game();

        let nedges = game.targets.len();
        let nverts = game.nvertices();

        let e: Vec<BoolView> = (0..nedges).map(BoolView).collect();
        let v: Vec<BoolView> = (0..nverts).map(BoolView).collect();

        let mut nocq = NOCQ::new(e, v, game);

        // make all edges defined true so recursion explores them
        let mut actions = MiniActions::new(nedges);
        for i in 0..nedges {
            actions.vals[i] = Some(true);
        }

        let mut expl = ();

        // run propagate (should not fail in this toy setup)
        nocq.propagate(&mut actions, &mut expl);

        // even cycle back-edge is e7 (6->4), should remain true
        assert_eq!(actions.vals[7], Some(true));
    }
}
