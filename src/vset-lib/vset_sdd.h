/*
 * vset_sdd.h
 *
 *  Created on: Jun 20, 2019
 *      Author: lieuwe
 */

#ifndef SRC_VSET_LIB_VSET_SDD_H_
#define SRC_VSET_LIB_VSET_SDD_H_

//extern "C" {
#include "/home/lieuwe/sdd-package-2.0/libsdd-2.0/include/sddapi.h"
//}

/* Bookkeep the variables that the SDD uses
 *
 */


struct vector_domain;

struct vector_set;

struct vector_relation;

extern SddManager* sisyphus;


/*
 * Version 2, each node is normalised to a vtree node.
 *  We do look at the corresponding vset.
  TODO
    + put iterator functionality in a separate file
    + Consistent naming
 *
 * iprime is for when the prime is the True node. In that case, iPrime goes from 0 to 2^m-1
 *   for some appropriate m
 *  Invariants:
 *  +  prime is not False
 */

struct sdd_model_iterator {
	//vset_t vset; //obsolete
	SddNode* root;
	//Vtree* vtree; //obsolete
	unsigned int i;
	//int* e; // obsolete
	int finished;

	//unsigned int iprime; // obsolete
	//unsigned int isub;   // obsolete
	//unsigned int primeFinished; // obsolete
	//unsigned int subFinished;   // obsolete
	unsigned int var_is_used;
};

// TODO none of the functions need mas by reference except sdd_next_model
struct sdd_mit_master {
	vset_t vset;
	struct sdd_model_iterator* nodes;
	int* e;
	unsigned int finished;
};

// TODO upgrade to long long unsigned int value, if things get out of hand, or to a list
void sdd_set_vtree_value_rec(const Vtree* tree, const unsigned int value, int* e, const unsigned int varsDone);

// Takes a tree node with <= 32 variables, and a 32-bit integer v
// Sets the e[var] = v[var] for every variable in the vtree
void sdd_set_vtree_value(const Vtree* tree, unsigned int v, int* e);

void sdd_get_iterator_rec(struct sdd_mit_master*, SddNode*, Vtree*);

struct sdd_mit_master sdd_get_iterator(vset_t);

void sdd_model_restart(struct sdd_mit_master*, Vtree*);

void sdd_mit_free_old(struct sdd_model_iterator* it);

void sdd_mit_free(struct sdd_mit_master);

/* Increments to the next model, if possible.
 * Otherwise, sets   it->finished = 1
 * TODO
 * + Refactor so that a sdd_model_iterator struct is normalised to a vtree node.
 *     That way, a lot of allocation and deallocation can be prevented
 */
void sdd_next_model(struct sdd_mit_master*);

//void sdd_next_model(struct sdd_model_iterator* it);

void small_enum(vset_t src);

static void set_add(vset_t src, const int* e);

#endif /* SRC_VSET_LIB_VSET_SDD_H_ */
