/******************************************************************

Copyright Michael Bailey 2019

Python bindings for RandGen.cpp
Generates random SAT problems

******************************************************************/

#include <Python.h>
#include <arrayobject.h>
#include <time.h>
#include "RandGen.h"


PyDoc_STRVAR(randSAT_get_problem_doc, "get_problem(num_vars, base_lits_pc, var_lits_pc, verbosity=0)");
PyObject* randSAT_get_problem(PyObject* self, PyObject* args, PyObject* kwargs) {
	int num_vars = 10, base_lits_pc = 3, var_lits_pc = 1, verb = 0;

	/* Parse positional and keyword arguments */
	static char* keywords[] = { "num_vars", "base_lits_pc", "var_lits_pc", "verbosity", NULL };
	if (!PyArg_ParseTupleAndKeywords(args, kwargs, "iii|i", keywords, &num_vars, &base_lits_pc, &var_lits_pc, &verb)) 
		return NULL;

	/* Function implementation starts here */

	//npy_intp d[1] = { 4 };
	//PyObject* test = PyArray_SimpleNew(1, d, NPY_INT64);
	//if (verb >= 1) printf("Tested Numpy API...\n");

	double t0, t1;
	if (verb >= 1) t0 = (double)clock() / CLOCKS_PER_SEC;
	RandomGenerator rg(num_vars, base_lits_pc, var_lits_pc, verb);
	if (verb >= 1) {
		t1 = (double)clock() / CLOCKS_PER_SEC;
		printf("Create generator: %.8f s\n", t1 - t0);
		t0 = (double)clock() / CLOCKS_PER_SEC;
	}
	rg.fillWithClauses();
	if (verb >= 1) {
		t1 = (double)clock() / CLOCKS_PER_SEC;
		printf("Generate problem: %.8f s\n", t1 - t0);
		t0 = (double)clock() / CLOCKS_PER_SEC;
	}
	int typenum = sizeof(int) == 4 ? NPY_INT32 : NPY_INT64;
	npy_intp dims[2] = { rg.getMembership(), 2 };
	//if (verb >= 1) printf("nvars: %d,  nclauses: %d,  membership: %d\n", num_vars, rg.getNClauses(), rg.getMembership());
	int* list = rg.indexList();
	if (verb >= 1) {
		t1 = (double)clock() / CLOCKS_PER_SEC;
		printf("Create index list: %.8f s\n", t1 - t0);
		t0 = (double)clock() / CLOCKS_PER_SEC;
	}
	PyArrayObject* indexList = (PyArrayObject *)PyArray_SimpleNewFromData(2, dims, typenum, list);
	PyArray_ENABLEFLAGS(indexList, NPY_OWNDATA);
	if (verb >= 1) {
		t1 = (double)clock() / CLOCKS_PER_SEC;
		printf("Create PyArray: %.8f s\n", t1 - t0);
	}

	return Py_BuildValue("Nii", indexList, 2 * rg.getNVars(), rg.getNClauses());
}

void delete_BatchGenerator(PyObject* bgc) {
	delete (BatchGenerator*)PyCapsule_GetPointer(bgc, "BatchGenerator");
}

PyDoc_STRVAR(randSAT_newBatchGenerator_doc, "newBatchGenerator(batch_size, min_vars, max_vars, var_vars, min_lits = 3, lits_var = 2, model = false, batches_ahead = 2, go = True)");
PyObject* randSAT_newBatchGenerator(PyObject* self, PyObject* args, PyObject* kwargs) {
	int batch_size, min_vars, max_vars, var_vars, lits = 3, batches_ahead = 2;
	float lits_var = 2;
	bool go = true, return_model = false;
	/* Parse positional and keyword arguments */
	static char* keywords[] = {"batch_size", "min_vars", "max_vars", "var_vars", "lits", "lits_var", "model", "batches_ahead", "go", NULL };
	if (!PyArg_ParseTupleAndKeywords(args, kwargs, "iiii|ifpip", keywords, &batch_size, &min_vars, &max_vars, &var_vars, &lits, &lits_var, &return_model, &batches_ahead, &go))
		return NULL;
	//printf("PyCpp return_model = %d\n", return_model);

	return (PyObject *) PyCapsule_New(new BatchGenerator(batch_size, min_vars, max_vars, var_vars, lits, lits_var, return_model, batches_ahead, go), "BatchGenerator", (PyCapsule_Destructor)delete_BatchGenerator);
}


PyDoc_STRVAR(randSAT_getNextBatch_doc, "getNextBatch(batch_generator)");
PyObject* randSAT_getNextBatch(PyObject* self, PyObject* bgc) {
	BatchGenerator *bg = (BatchGenerator*) PyCapsule_GetPointer(bgc, "BatchGenerator");
	tuple<int*, int, int, int> batch = bg->getBatch();

	int typenum = sizeof(int) == 4 ? NPY_INT32 : NPY_INT64;
	npy_intp dims[2] = { get<1>(batch), 2 };
	//printf("get<1>(batch) = %d\n", get<1>(batch));
	PyArrayObject* indexList = (PyArrayObject*)PyArray_SimpleNewFromData(2, dims, typenum, get<0>(batch));
	PyArray_ENABLEFLAGS(indexList, NPY_OWNDATA);

	return Py_BuildValue("Nii", indexList, 2 * get<2>(batch), get<3>(batch));
}

PyDoc_STRVAR(randSAT_getNextBatchAndModel_doc, "getNextBatchAndModel(batch_generator)");
PyObject* randSAT_getNextBatchAndModel(PyObject* self, PyObject* bgc) {
	BatchGenerator* bg = (BatchGenerator*)PyCapsule_GetPointer(bgc, "BatchGenerator");
	tuple<int*, int, int, int, int*> batch = bg->getBatchAndModel();

	int typenum = sizeof(int) == 4 ? NPY_INT32 : NPY_INT64;
	npy_intp dims[2] = { get<1>(batch), 2 };
	PyArrayObject* indexList = (PyArrayObject*)PyArray_SimpleNewFromData(2, dims, typenum, get<0>(batch));
	PyArray_ENABLEFLAGS(indexList, NPY_OWNDATA);

	npy_intp mdims[1] = { get<2>(batch)};
	PyArrayObject* model = (PyArrayObject*)PyArray_SimpleNewFromData(1, mdims, typenum, get<4>(batch));
	PyArray_ENABLEFLAGS(model, NPY_OWNDATA);

	return Py_BuildValue("NiiN", indexList, 2 * get<2>(batch), get<3>(batch), model);
}

PyDoc_STRVAR(randSAT_batchReady_doc, "batchReady(batch_generator)");
PyObject* randSAT_batchReady(PyObject* self, PyObject* bgc) {
	BatchGenerator* bg = (BatchGenerator*)PyCapsule_GetPointer(bgc, "BatchGenerator");
	return Py_BuildValue("O", bg->batchReady() ? Py_True : Py_False);
}

PyDoc_STRVAR(randSAT_changeParameters_doc, "changeParameters(batch_generator, batch_size, min_vars, max_vars, var_vars, lits, lits_var, use_old = false)\n   All arguments optional except first and last");
PyObject* randSAT_changeParameters(PyObject* self, PyObject* args, PyObject* kwargs) {
	PyObject* capsule;
	int batch_size = -1, min_vars = -1, max_vars = -1, var_vars = -1, lits = -1;
	float lits_var = -1;
	bool use_old = false;
	static char* keywords[] = { "", "batch_size", "min_vars", "max_vars", "var_vars", "lits", "lits_var", "use_old", NULL };
	if (!PyArg_ParseTupleAndKeywords(args, kwargs, "i|iiiifp", keywords, &capsule, &batch_size, &min_vars, &max_vars, &var_vars, &lits, &lits_var, &use_old))
		return NULL;
	BatchGenerator* bg = (BatchGenerator*)PyCapsule_GetPointer(capsule, "BatchGenerator");
	bg->changeParameters(batch_size, min_vars, max_vars, var_vars, lits, lits_var, use_old);
	Py_RETURN_NONE;
}

PyDoc_STRVAR(randSAT_solveSAT_doc, "solveSAT(indices, nvars)");
PyObject* randSAT_solveSAT(PyObject* self, PyObject* args) {
	PyObject* list;
	int nvars;
	if (!PyArg_ParseTuple(args, "Oi", &list, &nvars))
		return NULL;

	int typenum = sizeof(int) == 4 ? NPY_INT32 : NPY_INT64;
	PyObject *npList = PyArray_FROMANY(list, typenum, 2, 2, NPY_CARRAY);
	int members = PyArray_DIM(npList, 0);

	int* model = solveSAT((int*)(PyArray_DATA(npList)), members, nvars);
	Py_DECREF(npList);

	if (model == NULL) Py_RETURN_NONE;

	npy_intp dims[2] = { members, 2 };
	PyArrayObject* npModel = (PyArrayObject*)PyArray_SimpleNewFromData(2, dims, typenum, model);
	PyArray_ENABLEFLAGS(npModel, NPY_OWNDATA);

	return (PyObject *)npModel;
}


/*
 * List of functions to add to randSAT in exec_randSAT().
 */
static PyMethodDef randSAT_functions[] = {
	{ "get_problem", (PyCFunction)randSAT_get_problem, METH_VARARGS | METH_KEYWORDS, randSAT_get_problem_doc },
	{ "newBatchGenerator", (PyCFunction)randSAT_newBatchGenerator, METH_VARARGS | METH_KEYWORDS, randSAT_newBatchGenerator_doc },
	{ "getNextBatch", (PyCFunction)randSAT_getNextBatch, METH_O, randSAT_getNextBatch_doc },
	{ "getNextBatchAndModel", (PyCFunction)randSAT_getNextBatchAndModel, METH_O, randSAT_getNextBatchAndModel_doc },
	{ "batchReady", (PyCFunction)randSAT_batchReady, METH_O, randSAT_batchReady_doc },
	{ "changeParameters", (PyCFunction)randSAT_changeParameters, METH_VARARGS | METH_KEYWORDS, randSAT_changeParameters_doc },
	{ "solveSAT", (PyCFunction)randSAT_solveSAT, METH_VARARGS, randSAT_solveSAT_doc },
	{ NULL, NULL, 0, NULL } /* marks end of array */
};

/*
 * Initialize randSAT. May be called multiple times, so avoid
 * using static state.
 */
int exec_randSAT(PyObject *module) {
	import_array();
    PyModule_AddFunctions(module, randSAT_functions);

    PyModule_AddStringConstant(module, "__author__", "Michael Bailey");
    PyModule_AddStringConstant(module, "__version__", "1.0.0");
    PyModule_AddIntConstant(module, "year", 2019);

    return 0; /* success */
}

/*
 * Documentation for randSAT.
 */
PyDoc_STRVAR(randSAT_doc, "The randSAT module");


static PyModuleDef_Slot randSAT_slots[] = {
    { Py_mod_exec, (void *)exec_randSAT },
    { 0, NULL }
};

static PyModuleDef randSAT_def = {
    PyModuleDef_HEAD_INIT,
    "randSAT",
    randSAT_doc,
    0,              /* m_size */
    NULL,           /* m_methods */
    randSAT_slots,
    NULL,           /* m_traverse */
    NULL,           /* m_clear */
    NULL,           /* m_free */
};

PyMODINIT_FUNC PyInit_randSAT() {
    return PyModuleDef_Init(&randSAT_def);
}
