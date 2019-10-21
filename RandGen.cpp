/******************************************************************

Copyright Michael Bailey 2019

Generates random SAT problems

******************************************************************/
#include "RandGen.h"
#include <math.h>
#include <stdlib.h>
#include <time.h>

//#define PROB_MODEL // when variable is independent and undetermined, allow .5 assignment
#ifdef PROB_MODEL
#define RAND_PROB .5
#else
#define RAND_PROB (int)(frand() < .5)
#endif


//using namespace Minisat;

RandomGenerator::RandomGenerator(int nvars, int blitperclause, int varlitperclause, bool return_model, int verb) :
	n_vars(nvars),
	n_clauses(0),
	list(NULL),
	return_model(true/*return_model*/),
	base_litsperclause(blitperclause),
	var_litsperclause(varlitperclause),
	gamma(varlitperclause > 0 ? exp(-((float)(nvars - base_litsperclause)) / varlitperclause) : 0)
	{
	solver = new Solver();
	solver->random_seed = time(NULL);
	solver->verbosity = verb;
	for (int i = 0; i < nvars; i++) solver->newVar(), aVars.push(i), varPlace.push(i);
	/*if (return_model)*/ model = (int*)malloc(sizeof(int) * nvars);
}

RandomGenerator::~RandomGenerator() {
	if (solver != NULL) delete solver;
	if (model != NULL) free(model);
}

/*CRef RandomGenerator::newClause(int nlits) {
	//list = NULL;
	if (nlits < 0) nlits = gamma == 0 ? base_litsperclause : base_litsperclause - var_litsperclause * log(drand() * (1 - gamma) + gamma);
	assert(nlits <= n_vars);
	vec<Lit> clits(nlits);
	
	for (int i = 0; i < nlits; i++) {
		Var v = irand(n_vars);
		for (int j = 0; j < i; j++) {
			if (var(clits[j]) == v) {
				v++;
				if (v >= n_vars) v = 0;
				j = 0;
			}
		}
		clits[i] = mkLit(v, drand() < .5);
	}

	CRef cr = solver->addClauseGet_(clits, false);
	if (cr != CRef_Undef && cr != CRef_Dummy)
		for (int i = 0; i < nlits; i++)
			vecList.push(tuple<Lit, int>(clits[i], n_clauses));
	n_clauses++;
	list = NULL;
	return cr;
}*/

// Returns CRef_Dummy if clause succesfully added without conflict
// If clause could not be added (or SAT could not be determined), returns CRef_Undef
// If added clause created conflict, returns a CRef to it
CRef RandomGenerator::tryNewClause(int nlits, int nof_conflicts) {
	//if (n_vars < base_litsperclause) return CRef_Undef;
	if (nlits < 0) nlits = gamma == 0 ? base_litsperclause : base_litsperclause - var_litsperclause * log(drand() * (1 - gamma) + gamma);
	int avs = aVars.size();
	assert(base_litsperclause <= avs);
	if (nlits > avs) nlits = avs;

	vec<Lit> clits(nlits);
	
	for (int i = 0; i < nlits; i++) {
		int p = irand(avs);
		Var v = aVars[p];
		for (int j = 0; j < i; j++) {
			if (var(clits[j]) == v) {
				if (++p >= aVars.size()) p = 0;
				v = aVars[p];
				j = 0;
			}
		}
		if (solver->assigns[v] != l_Undef) {
			//printf("\a\n!!!Adding determinate literal to clause!!!\n");
			finish_var(v, solver->assigns[v] == l_True);
			if (--avs < nlits) return CRef_Undef;
			i--;
			continue;
		}
		clits[i] = mkLit(v, drand() < .5);
	}

	CRef cr = solver->addClauseGet_(clits, true);
	if (cr == CRef_Undef) {
		for (int i = 0; i < clits.size(); i++) finish_lit(~clits[i]);
		printf("\a\nWhoops! Couldn't add clause.\n");
		return CRef_Undef;
	}
	
	lbool ok = solver->search(nof_conflicts);
	if (ok == l_True) {
		/*if (return_model)*/ store_model();
		solver->cancelUntil(0);
		int ts = solver->trail.size();
		for (int i = 0; i < ts; i++)
			if (varPlace[var(solver->trail[i])] >= 0)
				finish_lit(solver->trail[i]);
		for (int i = 0; i < nlits; i++)
			vecList.push(tuple<Lit, int>(clits[i], n_clauses));
		n_clauses++;
		return CRef_Dummy;
	}
	// else: ok == false
	// contradiction; clits must all be false
	for (int i = 0; i < clits.size(); i++) finish_lit(~clits[i]);
	return cr;
}

// Stores only those values which are not already fixed
void RandomGenerator::store_model() {
	for (int i = 0; i < aVars.size(); i++) model[aVars[i]] = solver->value(aVars[i]) == l_True ? 1 : 0;
}

void RandomGenerator::rebuildSolver() {
	int v = solver->verbosity;
	delete solver;
	solver = buildSolver(vecList, n_vars, &varPlace, model, v);
	bool ok = solver->solve();
	solver->cancelUntil(0);
	if (!ok) {
		printf("\a\nRebuilt Solver not ok!!!\n");
	}
}

// Internal state may not be valid after calling:
// Eg., might have learned conflict clauses which no longer apply after removing/flipping last clause
// Eg., watchlists might be wrong after flipping last claue
void RandomGenerator::fillWithClauses(bool flip_last_clause) {
	int n = 0;
	while(n < 1000) {
		if (aVars.size() < base_litsperclause) {
			//printf("--- Not enough indeterminates. Finishing...\n", n-1);
			return;
		}
		//printf("Clause %d ", n);
		CRef cr = tryNewClause();
		for (int i = 0; cr != CRef_Dummy; i++) {
			//printf(": Conflict!\n",n);
			//printf("--- %d indeterminate.\n", aVars.size());
			if (i >= retries || aVars.size() < base_litsperclause) {
				//printf("--- Finishing...\n");
				return;
			}
			//if (n<1000) printf("(%d)",n);
			//printf("--- Restricting and retrying...\n",n);
			rebuildSolver();
			cr = tryNewClause();
		}
		//printf(": %d indeterminate.\n", aVars.size());
		n++;
	}
}

int* RandomGenerator::indexList(int firstClause, int firstVar, int totalVar, int * output) {
	int m = getMembership();
	if (output == NULL)
		list = (int *)malloc(m * 2 * sizeof(int));
	else if (list != NULL) return (int *)memcpy((void*)output, (void*)list, m * 2 * sizeof(int));
	else list = output;
	if (totalVar < 0) totalVar = n_vars;

	int* lp = list;
	for (int i = 0; i < m; i++, lp += 2) {
		Lit l = get<0>(vecList[i]);
		int q = sign(l) ? 2 * totalVar - (var(l) + firstVar + 1) : var(l) + firstVar;
		lp[0] = q;
		lp[1] = get<1>(vecList[i]) + firstClause;
	}

	return list;
}

// Makes a batch and writes it to the buffer
void BatchGenerator::makeBatch() {

	unique_lock<mutex> lk(small_mutex);
	// Copying (thread-unsafe) parameters to function scope:
	int bw = batch_write % MAX_BATCHES;
	int batch_size = this->batch_size;
	int min_vars = this->min_vars;
	int max_vars = this->max_vars;
	int var_vars = this->var_vars;
	int lits = this->lits;
	float lits_var = this->lits_var;
	making_batch = true;
	lk.unlock();

	unique_lock<mutex> buffer_lock(big_mutex);

	if (return_model) {
		{MEMSAFE models[bw] = (int*)malloc(sizeof(float) * batch_size);
		model_alloc = batch_write + 1; }
	}

	float gamma = var_vars == 0 ? 0 : exp(-((float)(max_vars - min_vars)) / var_vars);

	int members_sofar = 0, clauses_sofar = 0;
	
	vec<int> p_members;
	for (int vars_sofar = 0, nvars; vars_sofar < batch_size; vars_sofar += nvars) {
		nvars = gamma == 0 ? min_vars : min_vars - var_vars * log(frand() * (1 - gamma) + gamma);
		if (vars_sofar + nvars > batch_size) {
			nvars = batch_size - vars_sofar;
			if (nvars < min_vars) {// trivial subproblem
				if (return_model)
					for (; vars_sofar < batch_size; vars_sofar++)
						models[bw][vars_sofar] = RAND_PROB;
				break;
			}
		}

		RandomGenerator rg(nvars, lits, lits_var, return_model);
		//printf("Generating problem...\n");
		rg.fillWithClauses();
		//printf("%d variables unfixed in model.\n", rg.aVars.size());
		int* list;
		{MEMSAFE list = rg.indexList(clauses_sofar, vars_sofar, batch_size);
		lists.push(list);}

		if (return_model) {
			memcpy(models[bw] + vars_sofar, rg.model, nvars * sizeof(int));
			{MEMSAFE free(rg.model);
			rg.model = NULL;}
		}

		/*printf("--Testing subproblem...  ");
		if (testSAT(list, rg.getMembership(), batch_size)) printf("SAT\n");
		else printf("UNSAT!!!\n");*/

		
		{MEMSAFE p_members.push(rg.getMembership()); }
		members_sofar += rg.getMembership();
		clauses_sofar += rg.getNClauses();

		//printf("Subproblem... nvars %d, members %d\n", nvars, rg.getMembership());
	}

	{MEMSAFE batches[bw] = (int*)malloc(members_sofar * sizeof(array<int, 2>*));
	batch_alloc = batch_write + 1; }
	for (int i = 0, pos = 0; i < lists.size(); pos += p_members[i], i++) {
		memcpy(batches[bw] + 2 * pos, lists[i], sizeof(array<int, 2>) * p_members[i]);
		{MEMSAFE free(lists[i]);
		lists[i] = NULL;}
	}

	{MEMSAFE lists.clear(); }

	/*printf("Testing batch...  ");
	if (testSAT(list, members_sofar, batch_size)) printf("SAT\n");
	else printf("UNSAT!!!\n");*/

	//printf("\nTesting batch model...  ");
	/*if (!testSAT(batches[bw], members_sofar, batch_size, 0, models[bw])) {
		printf("\a ERROR!!! Model failed!\n");
		printf(" Trying unmodeled solve...");
		if (testSAT(batches[bw], members_sofar, batch_size, 0)) printf(" SAT????\n");
		else printf(" UNSAT!\n");
	}*/

	
	//while (batch_write - batch_read > batches_ahead) rw_cond.wait(lk);
	
	lk.lock();
	n_vars[bw] = batch_size;
	n_clauses[bw] = clauses_sofar;
	members[bw] = members_sofar;
	//printf("Members: %d\n", members_sofar);
	batch_write++;
	making_batch = false;
	lk.unlock();
	rw_cond.notify_all();
	buffer_lock.unlock();
}

void BatchGenerator::loopMakeBatch(int max) {
	unique_lock<mutex> lk(small_mutex);
	while (batch_write != max && !end){
		while (batch_write - batch_read > batches_ahead || !go) rw_cond.wait(lk);
		lk.unlock();
		rw_cond.notify_all();
		makeBatch();
		lk.lock();
	}
	go = false;
}

bool BatchGenerator::batchReady() {
	unique_lock<mutex> lk(small_mutex);
	return batch_write > batch_read;
}

tuple<int *, int, int, int> BatchGenerator::getBatch() {
	unique_lock<mutex> lk(small_mutex);
	while (batch_read >= batch_write) rw_cond.wait(lk);
	tuple<int*, int, int, int> r(batches[batch_read % MAX_BATCHES], members[batch_read % MAX_BATCHES], n_vars[batch_read % MAX_BATCHES], n_clauses[batch_read % MAX_BATCHES]);
	if (return_model) free(models[batch_read % MAX_BATCHES]);
	batch_read++;
	lk.unlock();
	rw_cond.notify_all();
	return r;
}

tuple<int*, int, int, int, int*> BatchGenerator::getBatchAndModel() {
	unique_lock<mutex> lk(small_mutex);
	while (batch_read >= batch_write) rw_cond.wait(lk);
	int br = batch_read % MAX_BATCHES;
	tuple<int*, int, int, int, int*> r(batches[br], members[br], n_vars[br], n_clauses[br], models[br]);
	batch_read++;
	lk.unlock();
	rw_cond.notify_all();
	return r;
}

void BatchGenerator::threadLoop(BatchGenerator* bg) {
	bg->loopMakeBatch();
}

void BatchGenerator::start() {
	unique_lock<mutex> lk(small_mutex);
	go = true;
	lk.unlock();
	rw_cond.notify_all();
}
void BatchGenerator::stop() {
	unique_lock<mutex> lk(small_mutex);
	go = false;
	lk.unlock();
	rw_cond.notify_all();
}

void BatchGenerator::changeParameters(int batch_size_, int min_vars_, int max_vars_, int var_vars_, int lits_, float lits_var_, bool use_old) {
	unique_lock<mutex> lk(small_mutex);
	if (batch_size_ > 0) batch_size = batch_size_;
	if (min_vars_ > 0) min_vars = min_vars_;
	if (max_vars_ > 0) max_vars = max_vars_;
	if (var_vars_ > 0) var_vars = var_vars_;
	if (lits_ > 0) lits = lits_;
	if (lits_var_ > 0) lits_var = lits_var_;
	if (!use_old) {
		if (making_batch) batch_read = batch_write + 1;
		else batch_read = batch_write;
	}
	lk.unlock();
	rw_cond.notify_all();
}


BatchGenerator::BatchGenerator(int batch_size, int min_vars, int max_vars, int var_vars, int lits, float lits_var, bool return_model, int batches_ahead, bool go) :
batch_size(batch_size), min_vars(min_vars), max_vars(max_vars), var_vars(var_vars), lits(lits), lits_var(lits_var), batches_ahead(batches_ahead), go(go)
{
	this->return_model = true;// return_model;
	//printf("BatchGenerator constructor: batch_size %d, min_vars %d, max_vars %d, var_vars %d, lits %d, lits_var %f\n", batch_size, min_vars, max_vars, var_vars, lits, lits_var);
	//printf("return_model = %d, this->return_model = %d\n", return_model, this->return_model);
	srand(time(NULL));
	workThread = thread(threadLoop, this);
}

BatchGenerator::~BatchGenerator() {
	unique_lock<mutex> lk1(small_mutex), lk2(alloc_mutex);
	end = true;
	for (int i = batch_read; i < batch_alloc; i++) delete batches[i % MAX_BATCHES];
	if (return_model) for (int i = batch_read; i < model_alloc; i++) delete models[i % MAX_BATCHES];
	for (int i = 0; i < lists.size(); i++) if (lists[i] != NULL) free(lists[i]);
	lk1.unlock(), lk2.unlock();
	workThread.join();
}

Solver* buildSolver(int* list, int members, int nvars, int verbosity) {
	Solver &s = *(new Solver());
	s.verbosity = verbosity;
	for (int i = 0; i < nvars; i++) s.newVar();
	vec<Lit> cl;
	for (int* pos = list, cn = list[1]; pos < list + 2 * members; pos += 2) {
		if (*(pos + 1) != cn) {
			s.addClause(cl);
			cl.clear();
			cn = *(pos + 1);
		}
		Lit l;
		if (*pos < nvars) l = mkLit(*pos);
		else l = mkLit(2 * nvars - 1 - *pos, true);
		cl.push(l);
	}
	s.addClause(cl);
	return &s;
}

Solver* buildSolver(const vec<tuple<Lit, int>>& vecList, int nvars, vec<int> *vp, int * model, int verbosity) {
	//printf("Building Solver from vecList...\n");
	Solver& s = *(new Solver());
	s.verbosity = verbosity;
	for (int i = 0; i < nvars; i++) s.newVar();
	vec<Lit> cl;
	bool cSAT = false;
	//printf("{");
	for (int i = 0, m = vecList.size(), cn = get<1>(vecList[0]); i < m; i++) {
		if (get<1>(vecList[i]) != cn) {
			//printf("\b}\n{");
			if (!cSAT) s.addClause(cl);
			cl.clear();
			cn = get<1>(vecList[i]);
			cSAT = false;
		}
		if (!cSAT) {
			Lit l = get<0>(vecList[i]);
			if (vp != NULL) {
				Var v = var(l);
				if ((*vp)[v] < 0) {
					if (sign(l) == (bool)model[v]) {
						//printf("X,");
						continue; // literal is false, remove
					}
					else {
						//printf("T,");
						cSAT = true; // literal is true, clause is trivial, skip clause
					}
				}
				else {
					//printf(sign(l) ? "-" : "+");
					//printf("%d,", v);
				}
			}
			cl.push(l);
		}
		//else printf("-,");
	}
	if (!cSAT) s.addClause(cl);
	//printf("\b}\n");
	return &s;
}

bool testSAT(int* list, int members, int nvars, int verbosity, int* model) {
	if (model == NULL) {
		Solver* s = buildSolver(list, members, nvars, verbosity);
		bool r = s->solve();
		delete s;
		return r;
	}
	else { // Check this particular model
		//printf("Hi\n");
		bool cSAT = false;
		for (int* pos = list, cn = list[1]; pos < list + 2 * members; pos += 2) {
			if (*(pos + 1) != cn) {
				if (!cSAT) return false;
				cn = *(pos + 1);
				cSAT = false;
				//printf("Clause %d\n", cn);
			}
			if (!cSAT) {
				bool sn;
				int var;
				if (*pos < nvars) var = *pos, sn = true;
				else var = 2 * nvars - 1 - *pos, sn = false;
				if (model[var] == (int)sn) cSAT = true;
			}
		}
		return true;
	}
}

int* solveSAT(int* list, int members, int nvars, int verbosity) {
	Solver* s = buildSolver(list, members, nvars, verbosity);
	int* model = NULL;
	if (s->solve()) {
		model = (int*)malloc(sizeof(int) * nvars);
		for (int i = 0; i < nvars; i++) model[i] = (int)(s->model[i] == l_True);
	}
	delete s;
	return model;
}


// main function for testing without python:

int main() {
	{
		printf("Creating BatchGenerator...\n");
		BatchGenerator bg(100, 10, 10, 0, 3, 2.0, true);
		printf("Getting first batch and model...\n");
		tuple<int*, int, int, int, int*> batch1 = bg.getBatchAndModel();
		printf("Getting second batch and model...\n");
		tuple<int*, int, int, int, int*> batch2 = bg.getBatchAndModel();
		printf("Destroying BatchGenerator...\n");
	}
	int i=0;
	while (++i < 3){
#ifdef _MSC_VER
		system("pause");
#else
		system("read");
#endif
		printf("Creating single problem generator...\n");
		RandomGenerator rg(10, 3, 0, false);
		printf("Generating problem and model...\n");
		rg.fillWithClauses();
		printf("Saving in sparse form...\n");
		int* list = rg.indexList();
		printf("Deleting RandomGenerator...\n");
		free(list);
	}
	printf("Done");
}



