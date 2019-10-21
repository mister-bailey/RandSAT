/******************************************************************

Copyright Michael Bailey 2019

Generates random SAT problems

******************************************************************/
#pragma once

#define RandGen
#include "core/Solver.h"
#include <array>
#include <thread>
#include <mutex>
#include <condition_variable>

#define MEMSAFE lock_guard<mutex> lg(alloc_mutex); if(this->end) return;

using namespace std;

using namespace Minisat;

inline float frand() { return rand() * 1.0 / RAND_MAX; }

class RandomGenerator {

	int const n_vars;
	int n_clauses;
	//int membership;
	int const base_litsperclause;
	int const var_litsperclause;

	int retries = 3; // 1; // number of times to try a different clause when we get conflict

	int * list;

	CRef badClause = CRef_Undef;

	float gamma;

	Solver *solver = NULL;

	bool return_model = false;

	inline double drand() { return solver->drand(solver->random_seed);}
	inline int irand(int size) { return solver->irand(solver->random_seed, size); }
	void store_model(); 

	inline void finish_var(Var v, bool value) {
		int vp = varPlace[v];
		if (vp < 0) return;
		varPlace[v] = -1;
		aVars.remove(vp);
		for (int i = v + 1; i < n_vars; i++) varPlace[i]--;
		if(return_model) model[v] = value;
	}
	// Set a literal to true, and removes its variable from contention
	inline void finish_lit(Lit l) { 
		finish_var(var(l), !sign(l));
	}

	void rebuildSolver();

public:

	vec<Var> aVars; // Variables available for new clauses (i.e., whose value isn't determined)
	vec<int> varPlace; // Reverse index into aVars
	vec<tuple<Lit, int>> vecList;

	RandomGenerator(int nvars, int blitperclause, int varlitperclause, bool return_model = false, int verb=0);
	~RandomGenerator();

	//CRef newClause(int nlits = -1);
	CRef tryNewClause(int nlits = -1, int nof_conflicts = -1);
	void fillWithClauses(bool flip_last_clause = false);

	int * indexList(int firstClause = 0, int firstVar = 0, int totalVar = -1, int* output=NULL);
	int getMembership();
	int getNVars();
	int getNClauses();

	int* model = NULL;

};

inline int RandomGenerator::getMembership() { return vecList.size(); }
inline int RandomGenerator::getNVars() { return n_vars; }
inline int RandomGenerator::getNClauses() { return n_clauses; }

#define MAX_BATCHES 100

class BatchGenerator {

	int batch_size; // In total variables

	int min_vars;
	int max_vars;
	int var_vars; // exponential width for problem size distribution

	int lits; // base lits per clause
	float lits_var;

	bool return_model;

	array<int *, MAX_BATCHES> batches;
	array<int, MAX_BATCHES> members;
	array<int, MAX_BATCHES> n_vars;
	array<int, MAX_BATCHES> n_clauses;
	array<int *, MAX_BATCHES> models;

	int batch_read = 0;
	int batch_write = 0;
	int batches_ahead = 2;

	int model_alloc = 0;
	int batch_alloc = 0;

	thread workThread;
	condition_variable rw_cond;
	mutex small_mutex;
	mutex big_mutex;
	mutex alloc_mutex;
	bool go = true;
	bool end = false;
	bool making_batch = false;
	vec<int*> lists; // temporary buffers, stored as members so destructor can free them

public:

	//static BatchGenerator* makeBatchGenerator();
	static void threadLoop(BatchGenerator* bg);

	BatchGenerator(int batch_size, int min_vars, int max_vars, int var_vars, int lits = 3, float lits_var = 2, bool return_model = false, int batches_ahead = 2, bool go = true);
	~BatchGenerator();

	void changeParameters(int batch_size = -1, int min_vars = -1, int max_vars = -1, int var_vars = -1, int lits = -1, float lits_var = -1, bool use_old = false);

	void makeBatch();
	void loopMakeBatch(int max = -1);
	bool batchReady();
	tuple<int *, int, int, int> getBatch();
	tuple<int*, int, int, int, int*> getBatchAndModel();
	void start();
	void stop();

	//int
};

Solver *buildSolver(int* list, int members, int nvars, int verbosity=0);
Solver* buildSolver(const vec<tuple<Lit, int>>& vecList, int nvars, vec<int> *varPlace = NULL, int *model = NULL, int verbosity=0);
bool testSAT(int* list, int nvars, int nclauses, int verbosity = 0, int* model = NULL);

int* solveSAT(int* list, int members, int nvars, int verbosity = 0);


