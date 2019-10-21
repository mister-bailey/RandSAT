/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2019 Michael Bailey

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#define _CRT_SECURE_NO_DEPRECATE
#include <math.h>
#include <stdio.h>

#include "mtl/Sort.h"
#include "core/Solver.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
#endif
#if BRANCHING_HEURISTIC == VSIDS
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
#endif
#if ! LBD_BASED_CLAUSE_DELETION
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
#endif
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
#if BRANCHING_HEURISTIC == CHB
static DoubleOption  opt_reward_multiplier (_cat, "reward-multiplier", "Reward multiplier", 0.9, DoubleRange(0, true, 1, true));
#endif


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
#endif
#if BRANCHING_HEURISTIC == VSIDS
  , var_decay        (opt_var_decay)
#endif
#if ! LBD_BASED_CLAUSE_DELETION
  , clause_decay     (opt_clause_decay)
#endif
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)
  //, prob_sharp (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , lbd_calls(0)
#if BRANCHING_HEURISTIC == CHB
  , action(0)
  , reward_multiplier(opt_reward_multiplier)
#endif

  , ok                 (true)
#if ! LBD_BASED_CLAUSE_DELETION
  , cla_inc            (1)
#endif
#if BRANCHING_HEURISTIC == VSIDS
  , var_inc            (1)
#endif
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (MinLitCmp(to_prop))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
 
    //activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    lbd_seen.push(0);
    picked.push(0);
    conflicted.push(0);
#if ALMOST_CONFLICT
    almost_conflicted.push(0);
#endif
#if ANTI_EXPLORATION
    canceled.push(0);
#endif
#if BRANCHING_HEURISTIC == CHB
    last_conflict.push(0);
#endif
#if PROP_STATS
	to_prop.push(0), to_prop.push(0);
	assign_order.push(INT_MAX);
#endif
    total_actual_rewards.push(0);
    total_actual_count.push(0);
    setDecisionVar(v, dvar);
    return v;
}

// If clause successfully added, returns clause reference
// If clause automatically satisfied (so not added, but no problems) returns CRef_Dummy
// If contradiction detected at this point, returns CRef_Undef
CRef Solver::addClauseGet_(vec<Lit>& ps, bool simplify)
{
	assert(decisionLevel() == 0);
	if (!ok) return CRef_Undef;

	// Check if clause is satisfied and remove false/duplicate literals:
	if (simplify) {
		sort(ps);
		Lit p; int i, j;
		for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
			if (value(ps[i]) == l_True || ps[i] == ~p)
				return CRef_Dummy;
			else if (value(ps[i]) != l_False && ps[i] != p)
				ps[j++] = p = ps[i];
		ps.shrink(i - j);
	}

	if (ps.size() == 0){
		ok = false;
		return CRef_Undef;
	}else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
		ok = (propagate() == CRef_Undef);
		//printf("\a!!Adding singleton!!\n");
        return ok ? CRef_Dummy : CRef_Undef; // 'ok' return value should not be used!
    }else{
		//if (verbosity >= 1) printf(" create...");
        CRef cr = ca.alloc(ps, false);
		//if (verbosity >= 1) printf(" add...");
        clauses.push(cr);
		//if (verbosity >= 1) printf(" attach...");
        attachClause(cr);
		return cr;
    }
}

// watches[lit] tracks occurences of ~lit 
void Solver::attachClause(CRef cr) {
	/*if (6411 == cr) {
		printf("PROBLEM CLAUSE!\n");
	}*/
    /*const*/
	//if (verbosity >= 1) printf("ATT..");
	Clause& c = ca[cr];
	
    assert(c.size() > 1);
	if (c.size() > 2) {
		if (c.learnt()) { // some variables in this clause may already be assigned. Must sort to invariant!
			// To begin, sort first 3
			sortFirst3(c);
			int num_undef = (assign_order[var(c[0])] == INT_MAX) + (assign_order[var(c[1])] == INT_MAX) + (assign_order[var(c[2])] == INT_MAX);
			
			for (int i = 3; num_undef < 3 && i < c.size(); i++) {
				int li = assign_order[var(c[i])];
				if (li > assign_order[var(c[0])]) {
					Lit p = c[2];
					c[2] = c[1];
					c[1] = c[0];
					c[0] = c[i];
					c[i] = p;
				}
				else if (li > assign_order[var(c[1])]) {
					Lit p = c[2];
					c[2] = c[1];
					c[1] = c[i];
					c[i] = p;
				}
				else if (li > assign_order[var(c[2])]) {
					Lit p = c[2];
					c[2] = c[i];
					c[i] = p;
				}
				if (li == INT_MAX) num_undef++;
			}
			if (value(c[2]) == l_False) {
#if PROP_TRUES
				if (value(c[1]) != l_True) incrementProp(c[0]);
#else
				incrementProp(c[0]);
#endif
				incrementProp(c[1]);
			}
		}
		watches[~c[2]].push(Watcher(cr, c[0]));
	} else {
		if (assign_order[var(c[1])] > assign_order[var(c[0])]) std::swap(c[0], c[1]);
#if PROP_TRUES
		if (value(c[1]) != l_True) incrementProp(c[0]);
#else
		incrementProp(c[0]);
#endif
		incrementProp(c[1]);
	}
	watches[~c[0]].push(Watcher(cr, c[1]));
	watches[~c[1]].push(Watcher(cr, c[0]));

    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);

	if (c.size() == 2 || value(c[2]) == l_False) {
		// Assuming invariant holds!
#if PROP_TRUES
		if (value(c[1]) != l_True) decrementProp(c[0]);
#else
		decrementProp(c[0]);
#endif
		decrementProp(c[1]);
	}

	if (strict) {
		remove(watches[~c[0]], Watcher(cr, c[1])); // Watcher equality doesn't depend on blockers!
		remove(watches[~c[1]], Watcher(cr, c[0]));
		if (c.size() > 2) remove(watches[~c[2]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
		if (c.size() > 2) watches.smudge(~c[2]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef; // MIKE: removed "picked"
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }




// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
// Note that the new invariant specified at propagate() is preserved
// We decrement to_prop[] where appropriate
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
			Lit      l = trail[c];
            Var      x  = var(l);
//#if !PROP_STATS
            uint64_t age = conflicts - picked[x];
            if (age > 0) {
                double reward = ((double) conflicted[x]) / ((double) age);
#if BRANCHING_HEURISTIC == LRB
#if ALMOST_CONFLICT
                double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
#else
                double adjusted_reward = reward;
#endif
                double old_activity = activity[x];
				// Trying out an alternative heuristic
                activity[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
				//activity[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);

                if (order_heap.inHeap(x)) {
                    if (activity[x] > old_activity)
                        order_heap.decrease(x);
                    else
                        order_heap.increase(x);
                }
#endif
                total_actual_rewards[x] += reward;
                total_actual_count[x] ++;
            }


#if ANTI_EXPLORATION
            canceled[x] = conflicts;
#endif
//#endif
            
			assign_order[x] = INT_MAX;

			if (assigns[x] != l_Undef) {
				assigns[x] = l_Undef;

#if PROP_STATS
				for (Watcher* w = (Watcher*)watches[l], *end = w + watches[l].size(); w != end; w++) {
					Clause& c = ca[w->cref];
					//if (c.size() == 2) continue;
					// By invariant, we only need check if c[2] == l:
					if (c.size() > 2 && c[2] == l) decrementProp(c[0]), decrementProp(c[1]);
					/*Lit c0 = c[0], c1 = c[1], c2 = c[2];
					if (l_Undef == value(c2) && l_Undef == value(c1) && l_Undef == value(c0)) {
						if (c0 != l) decrementProp(c0);
						if (c1 != l) decrementProp(c1);
						if (c2 != l) decrementProp(c2);
					}*/
				}
#if PROP_TRUES
				Lit p = ~l;
				for (Watcher* w = (Watcher*)watches[p], *end = w + watches[p].size(); w != end; w++) {
					Clause& c = ca[w->cref];
					// By the invariant, this should be enough:
					if (c[1] == p) incrementProp(c[0]);
					/*if (c.size() == 2) {
						if (c[1] == p) incrementProp(c[0]);
						continue;
					}
					// size > 2
					if (c[1] == p) incrementProp
					*/
				}

#endif
			}
#endif
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(l);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

	// Semirandom distribution:
	Var v;
	while (!order_heap.empty() && (value(v = order_heap[0]) != l_Undef || !decision[v])) order_heap.removeMin();
	int i = 0;
	while (drand(random_seed) > .8)
		while (++i < order_heap.size() && (value(v = order_heap[i]) != l_Undef || !decision[v]));
	if (i < order_heap.size()) next = i == 0 ? order_heap.removeMin() : order_heap[i];


    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
			return lit_Undef;
        } else {
#if ANTI_EXPLORATION
            next = order_heap[0];
            uint64_t age = conflicts - canceled[next];
            while (age > 0) {
                double decay = pow(0.95, age);
                activity[next] *= decay;
                if (order_heap.inHeap(next)) {
                    order_heap.increase(next);
                }
                canceled[next] = conflicts;
                next = order_heap[0];
                age = conflicts - canceled[next];
            }
#endif
            next = order_heap.removeMin();
        }

	// MIKE : where they choose polarity
    //return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
	return next == var_Undef ? lit_Undef : mkLit(next, drand(random_seed) > probability(next));
}

double Solver::probability(Var v) {
	Lit lp = mkLit(v);
	// compute probability:
	int np = to_prop[toInt(lp)];
	int nn = to_prop[toInt(~lp)];
	/*double ep = pow(2, np);
	double en = pow(2, nn);
	return (ep - .5) / (ep + en - 1.0);*/
	return 1.0 / (1 + pow(2, nn - np));
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef conf, vec<Lit>& out_learnt, int& out_btlevel)
{
	CRef confl = conf;
	if (verbosity >= 3 && confl == CRef_Undef) printf("analyze called with CRef_Undef.\n");
    int pathC = 0;
    Lit p     = lit_Undef;
	out_btlevel = 0;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
		if (confl == CRef_Undef) {
			if (true) {
				printf("**********************\n* Error: Unfolding CRef_Undef!\n");
				printf("* Trail length: %d\n", trail.size());
				printf("* Decision level %d:  %d -- %d\n", decisionLevel(), trail_lim[decisionLevel()-1], trail.size()-1);
				printf("* Decision Literal %d (Var %d)\n", trail[trail_lim[decisionLevel()-1]], var(trail[trail_lim[decisionLevel()-1]]));
				printf("* -- While unfolding Literal %d (Var %d)\n", p, var(p));
				printf("* %d variables, %d clauses, %d learntn", nVars(), nClauses(), nLearnts());
			}
			assert(confl != CRef_Undef); // (otherwise should be UIP)
		}
        Clause& c = ca[confl];

#if LBD_BASED_CLAUSE_DELETION
        if (c.learnt() && c.activity() > 2)
            c.activity() = lbd(c);
#else
        if (c.learnt())
            claBumpActivity(c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
#if BRANCHING_HEURISTIC == CHB
                last_conflict[var(q)] = conflicts;
#elif BRANCHING_HEURISTIC == VSIDS
                varBumpActivity(var(q));
#endif
                conflicted[var(q)]++;
                seen[var(q)] = 1;
				if (level(var(q)) >= decisionLevel()) {
					if (verbosity >= 3) printf("   Queuing Lit %d (Var %d) at level %d, index %d.\n", q, var(q), level(var(q)), assign_order[var(q)]);
					pathC++;
				}
				else {
					if (verbosity >= 3) printf("   ADDING Lit %d at level %d, index %d.\n", q, level(var(q)), assign_order[var(q)]);
					out_learnt.push(q);
					if (level(var(q)) > out_btlevel) out_btlevel = level(var(q));
				}
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
		if (verbosity >= 3) {
			printf("PathC = %d; UNFOLDING Lit %d (Var %d) to clause ", pathC, p, var(p));
			if (confl == CRef_Undef) printf("CRef_Undef!\n");
			else {
				printf("%d:", confl);
				printClause(confl, ca[confl]);
			}
		}
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;
	if (level(var(p)) < out_btlevel) out_btlevel = level(var(p));

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)
		// abstract_level records bitwise those levels (up to 32) which variables in out_learnt are decided at

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }
	// if (verbosity >= 3) printf("* Clause %d (length %d) conflicted at level %d, learning\n     clause of length %d and backtracking to level %d.\n", conf, ca[conf].size(), decisionLevel(), out_learnt.size(), out_btlevel);


#if ALMOST_CONFLICT
    seen[var(p)] = true;
    for(int i = out_learnt.size() - 1; i >= 0; i--) {
        Var v = var(out_learnt[i]);
        CRef rea = reason(v);
        if (rea != CRef_Undef) {
            Clause& reaC = ca[rea];
            for (int i = 0; i < reaC.size(); i++) {
                Lit l = reaC[i];
                if (!seen[var(l)]) {
                    seen[var(l)] = true;
                    almost_conflicted[var(l)]++;
                    analyze_toclear.push(l);
                }
            }
        }
    }
#endif
    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
	lbool val = value(p);
    assert(value(p) == l_Undef);
	if (assign_order[var(p)] < trail.size()) return;
    picked[var(p)] = conflicts;
#if ANTI_EXPLORATION
    uint64_t age = conflicts - canceled[var(p)];
    if (age > 0) {
        double decay = pow(0.95, age);
        activity[var(p)] *= decay;
        if (order_heap.inHeap(var(p))) {
            order_heap.increase(var(p));
        }
    }
#endif
    conflicted[var(p)] = 0;
#if ALMOST_CONFLICT
    almost_conflicted[var(p)] = 0;
#endif
	// Value assignment now takes place during propagate step!
    // assigns[var(p)] = lbool(!sign(p));
	assign_order[var(p)] = trail.size();
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
	/*if (verbosity >= 3 && var(p) == 380) {
		printf("Problem variable 380 is propagating!");
	}*/
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
/*
New invariant for (3)-watches:
If any unsatisfied clause has one or more of its watched literals set to false,
then: all of its unwatched literals are also false, its unwatched literals precede
its watched literals in the decision trail, and c[2] is the earliest assignment of the watched literals
*/

// TODO: Reduce to_prop when a clause becomes satisfied
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p == TRUE' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

		// Assignment now happens just before propagation!
		assigns[var(p)] = lbool(!sign(p));

		if (verbosity >= 3) printf("---> %d (%d)\n", p, var(p));

		// watches[lit] tracks occurences of ~lit, so ws tracks occurences of ~p (which is FALSE)
        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            /*Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }*/


            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      lf = ~p; // literal set to false

			if (verbosity >= 3) {
				printf("*WC %d", cr);
				if (78 == cr) detailClause(cr, c);
				else printClause(cr, c);
			}

			if (c.size() == 2) {
				// Make sure the false literal is data[1] WHY???
				if (c[0] == lf)
					c[0] = c[1], c[1] = lf;
				assert(c[1] == lf);
				Lit first = c[0];
				i++;
				*j++ = Watcher(cr, first);

				// If 0th watch is true, then clause is already satisfied.
				lbool vall = value(first);

				if (vall == l_True) continue;

				if (vall == l_False) {
					confl = cr;
					qhead = trail.size();
					// Copy the remaining watches:
					while (i < end)
						*j++ = *i++;
				}
				else {
					if (verbosity >= 3) printf("Unit %d (%d) :\n", first, var(first));
					uncheckedEnqueue(first, cr);
				}
			} else { // size > 2
				// MAINTAIN INVARIANT: if any watch is false, c[2] is the oldest assignment amongst the 3 watched literals

				i++;

				int fi; // index of current false lit
				int i0; // index of first other watch
				int i1; // index of second other watch
				if (c[0] == lf) fi = 0, i0 = 1, i1 = 2;
				else if (c[1] == lf) fi = 1, i0 = 0, i1 = 2;				
				else if (c[2] == lf) fi = 2, i0 = 0, i1 = 1;
				else {
					printf("Watched literal %d isn't among first 3 in clause %d!\n", lf, cr);
					printClause(cr, c);
					assert(false);
				}
				Lit l0 = c[i0], l1 = c[i1];
				lbool v0 = value(l0), v1 = value(l1);

				// If 0th or 1st watch is true, then clause is already satisfied.
				// May have to reorder literals to preserve invariant
				/*if (v0 == l_True) {
					if (fi == 2) { // No other watches are false, so move l0 == true to c[2]
						c[2] = l0;
						c[i0] = lf;
					} else if (value(c[2]) == l_Undef) { //  No other watches are false, so move l0 == true to c[2]
						c[2] = l0;
						c[i0] = l1;
					}
					*j++ = Watcher(cr, l0); // lf is still in c[0..2], so include this clause in watches[p]
					continue;
				}
				else if (v1 == l_True) {
					if (fi == 2) {
						c[2] = l1;
						c[i1] = lf;
					}
					/*else if (value(c[2]) == l_Undef) {
						c[2] = l1;
						c[i1] = l0;
					}*/
					/* *j++ = Watcher(cr, l1); // lf is still in c[0..2], so include this clause in watches[p]
					continue;
				}*/
				if (v0 == l_True || v1 == l_True) {
					// Sort to preserve invariant
					weakSortFirst3(c);
					*j++ = Watcher(cr, l1);
					continue;
				}

				Watcher w = Watcher(cr, l0);
				if (v0 == l_Undef && v1 == l_Undef) { //
					// Look for new watch:
					for (int k = 3; k < c.size(); k++)
						if (value(c[k]) != l_False) {
							c[fi] = c[k]; c[k] = lf;
							watches[~c[fi]].push(w); // new literal in first 3, so add this clause to watches of (negation of) this literal
							goto NextClause; // lf is no longer in first 3, so we don't increment j, and will overwrite this clause in watches[p]
						} // TODO: Separate l_True and l_Undef cases to get a better blocker

					// Did not find watch 
					// Make sure current literal is at c[2]
					if (fi != 2) c[2] = lf, c[fi] = l1;
					*j++ = w;
					incrementProp(l0);
					incrementProp(l1);
					continue;
				}
				*j++ = w;

				// By the invariant, clause is unit under assignment:
				// (Invariant is automatically preserved, by induction)
				// * Must make sure propagating literal is c[0]!
				if (v0 == l_False) {
					if (v1 == l_Undef) {
						// l1 is forced to be true
						if (i1 != 0) std::swap(c[0], c[i1]); // Making sure propagator is c[0]
						if (verbosity >= 3) {
							printf("Unit %d (%d) :\n", l1, var(l1));
						}
						uncheckedEnqueue(l1, cr); 
					} else {
						// this clause is a conflict
						confl = cr;
						qhead = trail.size(); // Note that none of the later lits have even been assigned!
						// Copy the remaining watches:
						while (i < end)
							* j++ = *i++;
					}
				}
				else {
					// l0 is forced to be true
					if (i0 != 0) { // Making sure propagator is c[0]
						Lit t = c[0];
						c[0] = l0, c[i0] = t;
					}
						if (verbosity >= 3) {
							printf("Unit %d (%d) :\n", l0, var(l0));
							printClause(cr, c);
						}
						uncheckedEnqueue(l0, cr);
				}
			}
        NextClause:;
        }
        ws.shrink(i - j);
#if PROP_TRUES
		for (i = (Watcher*)watches[~p], end = i + watches[~p].size(); i < end; i++) {
			CRef     cr = i->cref;
			Clause& c = ca[cr];
			// p is in c, and it's being set to TRUE

			if (c.size() == 2) {
				if (c[0] == p && value(c[1]) == l_Undef) {
					c[0] = c[1];
					c[1] = p;
					decrementProp(c[0]);
				}
				else if (value(c[0]) == l_Undef) decrementProp(c[0]);
				continue;
			}
			// size > 2
			lbool v2 = value(c[2]);
			if (v2 == l_Undef) { // Assuming invariant, means no false terms in the first 3
				if (c[0] == p) {
					c[0] = c[2];
					c[2] = p;
				}
				else {
					c[1] = c[2];
					c[2] = p;
				}
			}
			else if (v2 == l_False) {
				if (c[0] == p) {
					if (value(c[1]) == l_Undef) {
						c[0] = c[1];
						c[1] = p;
						decrementProp(c[0]);
					}
				}
				else if (value(c[0]) == l_Undef) decrementProp(c[0]); // c[1] == p
			}
			else { // v2 = True, nothing to do
			}

		}
#endif
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

int min(int a, int b) {
    return a < b ? a : b;
}

// Diagnostic:
inline bool Solver::detailClause(CRef cr, Clause& c, int maxlength) {
	if (c.learnt()) printf("  L ");
	else printf("  C ");
	if (c.size() > maxlength) {
		printf("\n");
		return false;
	}
	printf("{ ", cr);
	for (int n = 0; n < c.size(); n++) {
		vec<Watcher> &ws = watches[~c[n]];
		for (int i = 0; i < ws.size(); i++) {
			if (ws[i].cref == cr) {
				printf("w");
				continue;
			}
		}
		if (value(c[n]) == l_True) printf("+");
		else if (value(c[n]) == l_False) printf("-");
		else printf(".");
		printf("%d ", c[n]);
	}
	printf("}\n");
	return true;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
/*#if LBD_BASED_CLAUSE_DELETION
    vec<double>& activity;
    reduceDB_lt(ClauseAllocator& ca_,vec<double>& activity_) : ca(ca_), activity(activity_) {}
#else*/
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
//#endif
    bool operator () (CRef x, CRef y) { 
#if LBD_BASED_CLAUSE_DELETION
        return ca[x].activity() > ca[y].activity();
    }
#else
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
#endif
};
void Solver::reduceDB()
{
    int     i, j;
#if LBD_BASED_CLAUSE_DELETION
    sort(learnts, reduceDB_lt(ca));
#else
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity
    sort(learnts, reduceDB_lt(ca));
#endif

    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
#if LBD_BASED_CLAUSE_DELETION
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.activity() > 2 && !locked(c) && i < learnts.size() / 2)
#else
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
#endif
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
		//if (verbosity >= 1) printf("P");
        CRef confl = propagate();
		//if (verbosity >= 1) printf("x");

#if BRANCHING_HEURISTIC == CHB
        double multiplier = confl == CRef_Undef ? reward_multiplier : 1.0;
        for (int a = action; a < trail.size(); a++) {
            Var v = var(trail[a]);
            uint64_t age = conflicts - last_conflict[v] + 1;
            double reward = multiplier / age ;
            double old_activity = activity[v];
            activity[v] = step_size * reward + ((1 - step_size) * old_activity);
            if (order_heap.inHeap(v)) {
                if (activity[v] > old_activity)
                    order_heap.decrease(v);
                else
                    order_heap.increase(v);
            }
        }
#endif
        if (confl != CRef_Undef){
            // CONFLICT
			if (verbosity >= 3) {
				printf("Clause %d is a conflict at level %d:\n", confl, decisionLevel());
				Clause& c = ca[confl];
				printClause(confl, c);
			}
            conflicts++; conflictC++;
			
#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
            if (step_size > min_step_size)
                step_size -= step_size_dec;
#endif
			if (decisionLevel() == 0) { if (verbosity >= 2) printf("Returning l_False because conflict at decision level 0.\n"); return l_False; }

			learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

#if BRANCHING_HEURISTIC == CHB
            action = trail.size();
#endif

            if (learnt_clause.size() == 1){
				if (verbosity >= 3) {
					printf("   Learning { %d }, backtracking to level %d:\n", learnt_clause[0], backtrack_level);
				}
				uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
				Clause& clause = ca[cr];
				if (verbosity >= 3) {
					printf("   Learning conflict clause %d, backtracking to level %d:\n", cr, backtrack_level);
					printClause(cr, clause);
				}
                learnts.push(cr);
				//if (verbosity >= 1) printf("LRN..");
                attachClause(cr);
				//if (verbosity >= 1) printf("ATH..");
				if (verbosity >= 3) {
					printf("   Sorted clause %d:",cr);
					printClause(cr, clause);
				}
#if LBD_BASED_CLAUSE_DELETION
                
                clause.activity() = lbd(clause);
#else
                claBumpActivity(ca[cr]);
#endif
				//assert(value(learnt_clause[0]) == l_Undef);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

#if BRANCHING_HEURISTIC == VSIDS
            varDecayActivity();
#endif
#if ! LBD_BASED_CLAUSE_DELETION
            claDecayActivity();
#endif

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
#if ! RAPID_DELETION
                max_learnts             *= learntsize_inc;
#endif

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
			//printf("X");
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
			if (decisionLevel() == 0 && !simplify()) {
				if (verbosity >= 2) printf("Returning l_False because no conflict returned, but !simplify() failed.\n");
				return l_False;
			}

            if (learnts.size()-nAssigns() >= max_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
#if RAPID_DELETION
                max_learnts += 500;
#endif
            }
			//printf("Y");

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }
			//printf("Z");

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
#if BRANCHING_HEURISTIC == CHB
            action = trail.size();
#endif
			if (verbosity >= 3) printf("DECIDE LEVEL %d : Lit %d (Var %d)\n", decisionLevel(), next, var(next));
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

#if RAPID_DELETION
    max_learnts               = 2000;
#else
    max_learnts               = nClauses() * learntsize_factor;
#endif
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("LBD Based Clause Deletion : %d\n", LBD_BASED_CLAUSE_DELETION);
        printf("Rapid Deletion : %d\n", RAPID_DELETION);
        printf("Almost Conflict : %d\n", ALMOST_CONFLICT);
        printf("Anti Exploration : %d\n", ANTI_EXPLORATION);
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    // cancelUntil(0); // We want all the info!
    return status;
}

//=========================================
// Verifying the result

bool Solver::verify()
{
	if (verbosity >= 1) printf("*** Verifying %d clauses...\n", clauses.size());
	for (int i = 0; i < clauses.size(); i++) {
		Clause& c = ca[clauses[i]];
		//if (verbosity >= 2) printf("    Clause %d, size %d...", clauses[i], c.size());
		for (int j = 0; j < c.size(); j++) {
			if (modelValue(c[j]) == l_True) {
				//if (verbosity >= 2) printf("SAT! by Lit %d (Var %d)\n", c[j], var(c[j]));
				goto ClauseSatisfied;
			}
		}
		//if (verbosity >= 2) printf("\n");
		if (verbosity >= 2) {
			printf("Oops! Clause %d is unsatisfied!\n", clauses[i]);
			printClause(clauses[i], c);
		}
		return false;
	ClauseSatisfied:;
		
	}
	return true;
}
 

//======================================================
// Analyzes the model to test a probability metric
// Useful for tuning the metric and its parameters
//
// Precondition: Clauses are all sorted according to the invariant, with appropriate watch lists.
//      In other words, solver state is as it should be at the end of the search.
// Does not work with "assumptions".
//
void Solver::analyzeProbabilities() {
	//printf("Made it here 1\n");
	int n = nVars();
	assert(n = trail.size());

	// clearing to_prop and assigns
	for (int i = 0; i < n; i++) {
		to_prop[toInt(mkLit(Var(i)))] = 0;
		to_prop[toInt(~mkLit(Var(i)))] = 0;
		if (assigns[i] == l_Undef) printf("Oops! Var %d is unassigned!\n",i);
		//printf("assigns[%d] == %d\n", i, assigns[i]);
		assigns[i] = l_Undef;
	}

	// bins for statistics (how many trues and falses were estimated for each probability range)
	// [0-.1, .1-.2, ..., .9-1]
	// * WEIGHTED by amount of info
	int trues[10] = { 0,0,0,0,0,0,0,0,0,0 };
	int falses[10] = { 0,0,0,0,0,0,0,0,0,0 };
	int weights[10] = { 0,0,0,0,0,0,0,0,0,0 };

	// assigns[var(p)] = lbool(!sign(p));

	// size-2 clauses dealt with first:
	for (int i = 0; i < clauses.size(); i++) {
		CRef cr = clauses[i];
		Clause& c = ca[cr];
		if (c.size() == 2) {
			to_prop[toInt(c[0])]++;
			to_prop[toInt(c[1])]++;
		}
	}

	//printf("Made it here 2\n");
	//printf("%d decision levels.\n", trail_lim.size());

	// Going in order of the actual solution trail
	// But you could try a randomized order (or an ensemble of orders)
	// Currently computes probabilities only once per decision level
	// But you could compute them after each assignment
	for (int i = 0, level = 0; i < n; i++) {

		if (i == trail_lim[level] || i == n-1) {
			// Compute statistics
			// printf("Level %d\n", level);
			for (int j = 0; j < n; j++) {
				if (assigns[j] != l_Undef) continue;
				Var v = Var(j);
				Lit lp = mkLit(v), ln = ~lp;
				// compute probability:
				int np = to_prop[toInt(lp)];
				int nn = to_prop[toInt(ln)];

				double prob = probability(v);

				// put instance in the right bin:
				int bin = (int)(prob * 10);
				if (bin == 10) bin = 9;
				if (model[j] == l_True) trues[bin] += np + nn;
				else falses[bin] += np + nn;
				weights[bin] += np + nn;
			}

			level++;
		}

		

		Lit lit = trail[i], flit = ~lit;
		Var v = var(lit);
		assigns[v] = model[v];
		//if (level == 30) printf("Lit %d (Var %d) == l_False\n", flit, var(lit));

		Watcher* w, * end;
		for (w = (Watcher*)watches[lit], end = w + watches[lit].size(); w != end; w++) {
			CRef cr = w->cref;
			Clause& c = ca[cr];

			if (c.size() > 2 && c[2] == flit) {
				to_prop[toInt(c[0])]++;
				to_prop[toInt(c[1])]++;
			}
		}
#if PROP_TRUES
		//if (level == 30) printf("  Lit %d (Var %d) == l_True\n", lit, var(lit));
		for (w = (Watcher*)watches[flit], end = w + watches[flit].size(); w != end; w++) {
			CRef cr = w->cref;
			Clause& c = ca[cr];

			if (c[1] == lit && value(c[2]) == l_False) to_prop[toInt(c[0])]--;
		}
#endif
	}

	// Print analysis
	printf("*****************************************\n");
	printf(" Probability analysis\n");
	printf(" Heuristic evaluated at each decision level,\n    problem clauses only, weighted by amount of bits\n\n");
	printf(" Bin range    Frequency    Number of bits\n");
	for (int i = 0; i < 10; i++) {
		printf(" %1.1f - %1.1f", (1.0 * i) / 10.0, (1.0 * i + 1) / 10.0);
		if (weights[i] == 0) printf("       --- ");
		else printf("      %3.3f", trues[i] * 1.0 / weights[i]);
		printf("        %d\n", weights[i]);
	}

	/*printf("\n Testing the random number generator:\n\n");
	int bins[10] = { 0,0,0,0,0,0,0,0,0,0 };
	for (int i = 0; i < 1000; i++) {
		int bin = (int)(drand(random_seed) * 10);
		if (bin == 10) bin = 9;
		bins[bin]++;
	}
	for (int i = 0; i < 10; i++) {
		printf(" %1.1f - %1.1f", (1.0 * i) / 10.0, (1.0 * i + 1) / 10.0);
		printf("      %d\n", bins[i]);
	}*/

}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
	FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
