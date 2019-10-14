#ifndef _VSET_SDD_CPP_
#define _VSET_SDD_CPP_

/* SDD API for the LTSmin library
 *
 * Keep in mind that this library numbers its variables from 0...n-1,
 *   whereas SDDs number their variables 1...n
 *   This conversion is "hidden" from the calling LTSmin library,
 *   but this will cause a number of headaches
 */

/* status: Testing hypothesis
 *   Currently, in rel_update, we give the cb(.., e) function a state vector
 *   Currently this state vector spans all variables.
 * Hypothesis: We are supposed to return a state vector which spans only those variables
 *   that appear in the relation, as opposed to all variables.
 *   Phase 1: Test without separating rw, so that read and write variables are the same
 *   Phase 2: Test separating rw, taking into account to take the union of the sets
 *     (this is not a big hurdle, because the lists are sorted)
 * Oh my it looks like we're already implementing this thing! Let's switch our hypothesis:
 * hypothesis: We are supposed to return a full state vector
 * -----
 * Well I implemented it and it doesn't work either :-(
 */

#include <vset-lib/vdom_object.h>
#include "vset_sdd.h"
#include <alloca.h>
#include <inttypes.h>
#include <math.h>
#include <string.h>
#include "stdio.h"
#include <hre/user.h>
#include <hre-io/user.h>

//#include "vector.h"

/* 14/08/2019 Log
 * rel update seems not to add elements to rel
 * Caller seems to call rel_add_copy. Implement that and then check back here.
 *
 */

//#include "/home/lieuwe/sdd-package-2.0/libsdd-2.0/include/sddapi.h"

// The model 00000 is enumerated, while only the model 10000 is in the set :-(

static int xstatebits = 16;  // bits per integer
unsigned int enum_error = 0; // flag whether enum has gone wrong yet

struct vector_domain
{
    struct vector_domain_shared shared;

    int vectorsize;             // number of integers for each full state
    int *statebits;             // number of bits for each state variable
    int actionbits;             // number of bits for the action label

    /* The following are automatically generated from the above */

    int totalbits;              // number of bits for each full state
    int* state_variables;       // array of variable indices, representing the set of variables of the set
    int* prime_variables;       // array of variable indices, representing the set of primed variables
    //SDD* state_variables;        // set of all state variables
    //SDD* prime_variables;        // set of all prime state variables
    //SDD* action_variables;       // set of action label variables
};

struct vector_set {
	vdom_t dom;

	unsigned int n; // Placeholder variable for testing, Replace with SDD
	SddNode* sdd;

	int k;         // number of variables in this set, or -1 if the set contains all state variables
	               //   (is this the number of variables on which this set depends?)
	int* proj;     // array of indices of program variables used by this set

	int* state_variables;  // array of variable indices of bits, used to represent the variables of proj
	                       //   The arrays state_variables and proj may be different when a program variable is an integer.
	                       //   In that case, state_variables will contain xstatebits (=16) different variables to represent this integer
	unsigned int nstate_variables; // length of state_variables array

	unsigned int id;       // unique ID of this set
};

struct vector_relation {
	vdom_t dom;

	int r_k;     // number of read variables
	int w_k;      // number of write variables
	int* r_proj; // array  of read variable indices
	int* w_proj; // array of write variable indices

	int* state_variables; // array of bit-variable indices, the unprimed variables
	int* prime_variables; // array of bit-variable indices, the primed variables

	unsigned int id;      // unique ID of this relation

	SddNode* sdd;
};

struct vector_relation_ll;
struct vector_set_ll;
typedef struct vector_relation_ll* vrel_ll_t;
typedef struct vector_set_ll* vset_ll_t;

// A linked list structure for the vrel_t objects
// Necessary due to freak bug in ltsmin (or freak bug in this code?)
struct vector_relation_ll {
	vrel_t rel;
	unsigned int id;
	int r_k;
	int w_k;
	int* r_proj;
	int* w_proj;
	struct vector_relation_ll* next;
};

// A linked list structure for the vset_t objects
// Here we store which variables are currently relevant for this set
struct vector_set_ll {
	vset_t set;
	unsigned int id;
	int k;
	int* proj;
	vset_ll_t next;
};


vrel_ll_t first_vrel = 0;
vrel_ll_t last_vrel = 0;
vset_ll_t first_vset = 0;
vset_ll_t last_vset = 0;

void add_vrel(vrel_t rel) {
	if (first_vrel == 0) {
		first_vrel = malloc(sizeof(struct vector_relation_ll));
		last_vrel = first_vrel;
	}
	else {
		vrel_ll_t previous_last_vrel = last_vrel;
		last_vrel = malloc(sizeof(struct vector_relation_ll));
		previous_last_vrel->next = last_vrel;
	}
	last_vrel->rel = rel;
	last_vrel->id = rel->id;
	last_vrel->r_k = rel->r_k;
	last_vrel->w_k = rel->w_k;
	last_vrel->r_proj = rel->r_proj;
	last_vrel->w_proj = rel->w_proj;
	last_vrel->next = 0;
}

void add_vset(vset_t set) {
	if (first_vset == 0) {
		first_vset = malloc(sizeof(struct vector_set_ll));
		last_vset = first_vset;
	}
	else {
		vset_ll_t previous_last_vset = last_vset;
		last_vset = malloc(sizeof(struct vector_set_ll));
		previous_last_vset->next = last_vset;
	}
	last_vset->set = set;
	last_vset->id = set->id;
	last_vset->k = set->k;
	// TODO see if we can reduce this to last_vset->k
	last_vset->proj = malloc(sizeof(int)*set->dom->vectorsize);
	for (int i=0; i<set->k; i++) {
		last_vset->proj[i] = set->proj[i];
	}
}

// Returns the linked-list-relation struct with the given id.
// If the id is not present, returns the last relation in the linked list
vrel_ll_t get_vrel(unsigned int id) {
	if (first_vrel == 0) return (vrel_ll_t) 0;
	vrel_ll_t rel = first_vrel;
	while (rel->id != id && rel->next != 0) {
		rel = rel->next;
	}
	return rel;
}

vset_ll_t get_vset(unsigned int id) {
	if (first_vset == 0) return (vset_ll_t) 0;
	//printf("  [get vset] Start looking for %u:  ", id);
	vset_ll_t set = first_vset;
	while (set->id != id && set->next != 0) {
		//printf(" %u", set->id);
		set = set->next;
	}
	//printf(" Found %u.\n", set->id);
	return set;
}

void vset_set_domain_rel(vset_t dst, vrel_t rel) {
	vrel_ll_t rel_ll = get_vrel(rel->id);
	vset_ll_t set_ll = get_vset(dst->id);
	set_ll->k = rel_ll->w_k;
	if (rel_ll->w_k != -1) {
		memcpy(set_ll->proj, rel_ll->w_proj, sizeof(int) * rel_ll->w_k);
	}
}

// Adds the variables from the domain of src to the domain in dst
void vset_add_to_domain(vset_t dst, vset_t src) {
	vset_ll_t dst_ll = get_vset(dst->id);
	vset_ll_t src_ll = get_vset(src->id);
	if (dst_ll->k == -1) return;
	if (src_ll->k == -1) {
		dst_ll->k = -1;
		return;
	}
	int* proj_union = malloc(sizeof(int) * src->dom->vectorsize);
	int k_union = 0;
	int i_dst = 0;
	int i_src = 0;
	int i_union;
	while (i_dst < dst_ll->k && i_src < src_ll->k) {
		if (dst_ll->proj[i_dst] == src_ll->proj[i_src]) {
			proj_union[i_union] = dst_ll->proj[i_dst];
			i_dst++;
			i_src++;
		}
		else if (dst_ll->proj[i_dst] <= src_ll->proj[i_src]) {
			proj_union[i_union] = dst_ll->proj[i_dst];
			i_dst++;
		}
		else {
			proj_union[i_union] = src_ll->proj[i_src];
			i_src++;
		}
		i_union++;
	}
	k_union = i_union;
	if (k_union == src->dom->vectorsize) {
		k_union = -1;
	}
	else {
		memcpy(dst_ll->proj, proj_union, sizeof(int) * src->dom->vectorsize);
	}
	dst_ll->k = k_union;
	free(proj_union);
}

void vset_set_domain(vset_t dst, vset_t src) {
	vset_ll_t dst_ll = get_vset(dst->id);
	vset_ll_t src_ll = get_vset(src->id);
	dst_ll->k = src_ll->k;
	if (src_ll->k != -1) {
		memcpy(dst_ll->proj, src_ll->proj, sizeof(int) * src_ll->k);
	}
}

// (sdd_greeting_opt: for testing whether command line options work)
static int sdd_greeting_opt = 0; // Display a friendly greeting upon startup

struct poptOption sdd_options[] = {
    { "sdd_greeting", 0, POPT_ARG_INT, &sdd_greeting_opt, 0, "Display a friendly greeting upon startup", "<sdd_greeting_opt>"},
    POPT_TABLEEND
};

// Our approach uses one SDD manager, which we will call Sisyphys,
// after the Greek mythological figure, condemned to endlessly roll a boulder up a hill,
// only to see all his work undone, and to start over again from the bottom
SddManager* sisyphus = NULL;

// Returns an SDD in which all primes have value 0
SddNode* sdd_primes_zero() {
	SddNode* z = sdd_manager_true(sisyphus);
	for (SddLiteral v=2; v<= sdd_manager_var_count(sisyphus); v+=2) {
		z = sdd_conjoin(z, sdd_manager_literal(-v, sisyphus), sisyphus);
	}
	return z;
}

static SddModelCount set_count_exact(vset_t set) {
	SddNode* sur = set->sdd;
	// Set all prime variables to True
	// TODO use the sdd_primes_one function to achieve some speedup
	for (SddLiteral v = 2; v<=sdd_manager_var_count(sisyphus); v+=2) {
		sur = sdd_conjoin(sur, sdd_manager_literal(v, sisyphus), sisyphus);
	}
	/* Set all unused variables to True */
	vset_ll_t set_ll = get_vset(set->id);
	if (set_ll->k != -1) {
		int set_var = 0;
		int sdd_var = 1;
		for (int i=0; i<set->dom->vectorsize; i++) {
			if (set_var < set_ll->k && set_ll->proj[set_var] == i) {
					// Ok, these variables are used
					sdd_var += 2 * xstatebits;
					set_var += 1;
			}
			else {
				// These variables are not used, so set them to True
				for (int j=0; j<xstatebits; j++) {
					sur = sdd_conjoin(sur, sdd_manager_literal(sdd_var, sisyphus), sisyphus);
					sdd_var += 2;
				}
			}
		}
	}
	SddModelCount mc;
	mc = sdd_global_model_count(sur, sisyphus);
	return mc;
}

unsigned int sdd_literal_value(SddNode* x) {
	if (x == 0) return 0;
	if (sdd_node_is_literal(x)) {
		return sdd_node_literal(x) > 0 ? 1 : 0;
	}
	else {
		printf("What the hell, %lu is not a literal!\n", sdd_id(x));
		return 0;
	}
}

unsigned int sdd_literal_index(SddNode* x) {
	if (x == 0) return 0;
	if (sdd_node_is_literal(x)) {
		int lit = sdd_node_literal(x);
		return lit > 0 ? lit : -lit;
	}
	else {
		printf("What the hell, %lu is not a literal!\n", sdd_id(x));
		return 0;
	}
}

unsigned int sdd_literal_unprimed_index(SddNode* x) {
	if (x == 0) return 0;
	if (sdd_node_is_literal(x)) {
		int lit = sdd_node_literal(x);
		lit = lit > 0 ? lit : -lit;
		lit = (lit % 2 == 0) ? lit / 2 : (lit+1) / 2;
		return lit;
	}
	else {
		return 0;
	}
}

// Returns an SDD representing the literal litId (with litId in 1...n)
SddNode* getLiteral(int litId, unsigned int value, unsigned int primed) {
	int lit = litId > 0 ? litId : -litId;
	lit = primed ? 2*litId : 2*litId - 1;
	lit = value ? lit : -lit;
	return sdd_manager_literal(lit ,sisyphus);
}

/* Returns an SDD representing the conjunction of literals in "literals"
 *   with "literals" a list of (signed) variable indices. Example: With the following values,
 *       literals[0] == -5,
 *       literals[1] ==  6,
 *   we return the SDD (!5 & 6) is returned
 */
SddNode* sdd_getCubeLiterals(int* literals, unsigned int nVars) {
	SddNode* conj = sdd_manager_true(sisyphus);
	for (unsigned int i=0; i<nVars; i++) {
		conj = sdd_conjoin(conj, sdd_manager_literal(literals[i], sisyphus), sisyphus);
	}
	return conj;
}

void vset_exposition(vset_t set) {
	//printf("  [Set exposition] set %u = ", set->id); small_enum(set); printf("\n");
	//printf("    [Set exposition] set @%p\n", set->sdd);
	//printf("    [Set exposition] Models: %llu\n", set_count_exact(set));
	vset_ll_t set_ll = get_vset(set->id);
	printf("    [Set exposition] k=%i:  {", set_ll->k);
	for (int i=0; i<set_ll->k; i++) {
		printf(" %i", set_ll->proj[i]);
	}
	printf("}\n");
}

// printf the values of the relation
void vrel_exposition(vrel_t rel) {
	vrel_ll_t rel_ll = get_vrel(rel->id);
	SddModelCount mc = sdd_model_count(rel->sdd, sisyphus);
	printf("  [Rel exposition] rel %u |.|=%llu ", rel->id, mc);
	printf("  r_proj = {");
	if (rel_ll->r_k == -1)
		printf(" (all) ");
	else {
		for (int v=0; v<rel_ll->r_k; v++) {
			printf(" %u", rel_ll->r_proj[v]);
		}
	}
	printf(" }  w_proj = {");
	if (rel_ll->w_k == -1)
		printf(" (all) ");
	else {
		for (int v=0; v<rel_ll->w_k; v++) {
			printf(" %u", rel_ll->w_proj[v]);
		}
	}
	printf(" }\n");
}

/* Returns an SDD representing the conjunction of the literals with indices in "vars",
 *   with values in "values". Example:
 *   If vars[0] == 5, values[0] == 0, vars[1] == 6, values[1] == 1, then
 *   the SDD (!5 & 6) is returned.
 */
SddNode* sdd_getCube(int* vars, uint8_t* values, unsigned int nVars) {
	SddNode* conj = sdd_manager_true(sisyphus);
//	printf("[SDD getCube] Making cube of %u vars.\n", nVars);
//	printf("  [Sdd getCube]  Value: ");
	for (unsigned int i=0; i<nVars; i++) {
		//printf("  [SDD getCube] Cubing variable %i = %u.\n", vars[i], values[i]);
/*
		if (i % 16 == 0) {
			printf(" ");
		}
		printf("%u", values[i]);
*/
		conj = sdd_conjoin(conj, sdd_manager_literal(values[i] ? (vars[i] + 1) : -(vars[i] + 1), sisyphus), sisyphus);
		//printf("  [SDD getCube] The Sdd after %i literals:\n", i+1);
		//traverse(conj);
	}
//	printf("\n");
	//printf("\n  [SDD getCube] The SDD:");
	//traverse(conj);
//	printf("  [Sdd getCube] Models: %llu\n", sdd_model_count(conj, sisyphus));
	return conj;
}

// Returns whether the sets a,b are defined over disjoint sets of variables
unsigned int vset_domains_are_disjoint(vset_t a, vset_t b) {
	vset_ll_t a_ll = get_vset(a->id);
	vset_ll_t b_ll = get_vset(b->id);
	if (a_ll->k == -1 || b_ll->k == -1) {
		return 0;
	}
	// See if they have a common variable
	for (int v=0; v<a_ll->k; v++) {
		for (int w=0; w<b_ll->k; w++) {
			if (a_ll->proj[v] == b_ll->proj[w]) {
				//printf("  [vset domains disjoint] Sets %u and %u share variable %i\n", a->id, b->id, a_ll->proj[v]);
				return 0;
			}
		}
	}
	return 1;
}

unsigned int vset_domains_are_equal(vset_t a, vset_t b) {
	if (a->k != b->k) return 0;
	if (a->k == -1) return 1;
	for (int i=0; i<a->k; i++) {
		if (a->proj[i] != b->proj[i]) return 0;
	}
	return 1;
}

static vset_t set_create(vdom_t dom, int k, int* proj) {
	static unsigned int id = 0;
	//printf("[Sdd set create] id=%u  k = %i.\n", id, k);
	vset_t set = (vset_t) malloc(sizeof(struct vector_set));
	set->dom = dom;
	set->sdd = sdd_manager_false(sisyphus);
	set->k = k;
	set->id = id;
	id++;

	if (k == -1) {
		set->proj = NULL;
		set->state_variables = dom->state_variables;
		set->nstate_variables = dom->totalbits;
	}
	else {
		set->proj = malloc(sizeof(int[k]));
		memcpy(set->proj, proj, sizeof(int[k]));
		set->nstate_variables = xstatebits * k;
		set->state_variables = malloc(sizeof(uint32_t[set->nstate_variables]));
		uint32_t curvar = 0;
		int j = 0;
		int i_var = 0;
		for (int i=0; i<dom->vectorsize && j<k; i++) {
			if (i == proj[j]) {
				for (int x=0; x<dom->statebits[i]; x++) {
					set->state_variables[i_var] = curvar;
					i_var++;
					curvar += 2;
				}
				j++;
			}
			else {
				curvar += 2 * dom->statebits[i];
			}
		}

		/*
		printf("  Creating set on variables: {");
		for (unsigned int i=0; i<(unsigned int)k; i++) {
			printf("%i ", proj[i]);
		}
		printf("}.\n");
		 */
	}
	add_vset(set);

	if (set->id == 13) {

		/* A difficult set to enumerate, obtained through much sweat and perseverence
		int* e = malloc(xstatebits * dom->vectorsize);
        set_e(e,2,2,2,1,2); set_add(set, e); // Necessary
        set_e(e,2,2,2,0,0); set_add(set, e); // Necessary
        set_e(e,2,2,2,0,2); set_add(set, e); // Necessary
        set_e(e,2,2,2,0,1); set_add(set, e); // Necessary
        set_e(e,2,2,2,1,0); set_add(set, e); // Necessary
        set_e(e,2,2,2,1,1); set_add(set, e); // Necessary
        */
        //set_e(e,2,2,1,0,1); set_add(set, e);
        //set_e(e,2,2,1,1,1); set_add(set, e);
        //set_e(e,2,2,2,2,1); set_add(set, e);
        //set_e(e,2,4,2,2,1); set_add(set, e);
        //set_e(e,2,4,1,2,1); set_add(set, e);
        //set_e(e,2,3,2,2,1); set_add(set, e);
        //set_e(e,2,2,3,1,2); set_add(set, e);
        //set_e(e,2,2,4,1,2); set_add(set, e);
        //set_e(e,2,1,4,1,2); set_add(set, e);
        //set_e(e,2,1,2,1,0); set_add(set, e);
        //set_e(e,2,1,2,1,1); set_add(set, e);
        //set_e(e,3,2,3,0,0); set_add(set, e);
        //set_e(e,4,0,4,0,0); set_add(set, e);
        //set_e(e,4,2,4,0,0); set_add(set, e);
        //set_e(e,4,4,0,0,0); set_add(set, e);
        //set_e(e,4,4,2,0,0); set_add(set, e);
        //set_e(e,3,3,2,0,0); set_add(set, e);
        //set_e(e,2,2,2,2,0); set_add(set, e);
        //set_e(e,2,2,0,0,0); set_add(set, e);
        //set_e(e,2,2,0,1,0); set_add(set, e);
        //set_e(e,2,0,2,0,0); set_add(set, e);
        //set_e(e,2,0,2,0,1); set_add(set, e);
        //set_e(e,1,2,2,2,2); set_add(set, e);
        //set_e(e,1,2,1,2,1); set_add(set, e);
        //set_e(e,1,1,2,1,2); set_add(set, e);
        //set_e(e,2,2,3,0,2); set_add(set, e);
        //set_e(e,2,2,4,0,2); set_add(set, e);
        //set_e(e,2,0,4,0,2); set_add(set, e);
        //set_e(e,1,0,2,0,2); set_add(set, e);
        //set_e(e,2,4,0,2,0); set_add(set, e);
        //set_e(e,2,4,2,2,0); set_add(set, e);
        //set_e(e,2,3,2,2,0); set_add(set, e);
        //set_e(e,1,2,0,2,0); set_add(set, e);
        //set_e(e,1,1,1,1,1); set_add(set, e);
        //set_e(e,1,0,1,0,1); set_add(set, e);
        //set_e(e,1,1,0,1,0); set_add(set, e);
        //set_e(e,1,0,0,0,0); set_add(set, e);

        //small_enum(set);

        //sdd_save_as_dot("small_error.dot", set->sdd);


        //fflush(stdout);
        //getchar();
	}

	return set;
}

static void set_destroy(vset_t set) {
	printf("[Sdd] set destroy.\n");
	// :-(
	set->sdd = sdd_manager_false(sisyphus);
}

static vrel_t rel_create_rw(vdom_t dom, int r_k, int* r_proj, int w_k, int* w_proj) {
	static unsigned int id = 0;
	/*
	printf("[Sdd Relation create] id = %u\n", id);
	// Output the relation's variables
	printf("  Relation read: r_k=%i {", r_k);
	for (int i=0; i<r_k; i++) {
		printf("%i ", r_proj[i]);
	}
	printf("}\n  Relation write: w_k=%i {", w_k);
	for (int i=0; i<w_k; i++) {
		printf("%i ", w_proj[i]);
	}
	printf("}\n");
	 */

	vrel_t rel = (vrel_t) RTmalloc(sizeof(struct vector_relation));
	rel->dom = dom;
	rel->sdd = sdd_manager_false(sisyphus);
	rel->r_k = r_k;
	rel->w_k = w_k;
	rel->id = id;
	id++;
	/*
	if (rel->sdd == 0) {
		printf("  [Sdd relation create (id=%u)] sdd=0 :-(\n", rel->id);
	}
	else {
		printf("  [Sdd relation create (id=%u)] sdd=%p adr=%p :-)\n", rel->id, rel->sdd, rel);
	}
	 */
	rel->r_proj = malloc(sizeof(int) * r_k);
	rel->w_proj = malloc(sizeof(int) * w_k);
	memcpy(rel->r_proj, r_proj, sizeof(int) * r_k);
	memcpy(rel->w_proj, w_proj, sizeof(int) * w_k);

	// Compute a_proj (accessed projection), the union of the sets of read and write variables

	// Compute ro_proj (read-only): a_proj \ w_proj

	// Initialise the state variables (the unprimed variables, i.e. the bits that are read
	int state_vars[xstatebits * r_k];
	int curvar = 0; //
	int i=0, j=0, n=0;
	for (; i<dom->vectorsize && j<r_k; i++) {
		if (i == r_proj[j]) {
			for (int k=0; k<dom->statebits[i]; k++) {
				state_vars[n] = curvar;
				n++;
				curvar += 2;
			}
			j++;
		}
		else {
			curvar += 2 * dom->statebits[i];
		}
	}
	rel->state_variables = malloc(sizeof(int) * n);
	memcpy(rel->state_variables, state_vars, sizeof(int) * n);

	int prime_vars[xstatebits * w_k];
	curvar = 0;
	j = 0; n = 0;
	for (i=0; i<dom->vectorsize && j<w_k; i++) {
		if (i == w_proj[j]) {
			for (int k=0; k<dom->statebits[i]; k++) {
				prime_vars[n] = curvar + 1;
				n++;
				curvar += 2;
			}
			j++;
		}
		else {
			curvar += 2 * dom->statebits[i];
		}
	}
	rel->prime_variables = malloc(sizeof(int) * n);
	memcpy(rel->prime_variables, prime_vars, sizeof(int) * n);
	add_vrel(rel);
	//vrel_exposition(rel);

	return rel;
}

static void rel_destroy(vrel_t rel) {
//	printf("[Sdd] rel destroy.\n");
	// TODO like, deallocate or gc
	rel->sdd = sdd_manager_false(sisyphus);
}

/* TODO should we copy the state vector in reverse, or not? That is,
				arr[i_arr] = ( state[i_state] & (1 << (n)) ) ? 1 : 0;
				versus
				arr[i_arr] = ( state[i_state] & (1 << (sb-n-1)) ) ? 1 : 0;
 */
static void state_to_cube(vdom_t dom, int k, const int* proj, const int* state, uint8_t* arr) {
//	printf("[Sdd] state to cube, k=%i.\n", k);
	/*
    if (k == -1) {
        for (int i=0; i<dom->vectorsize; i++) {
            const int sb = dom->statebits[i];
            for (int n=0; n<sb; n++) *arr++ = (*state & (1LL<<(sb-n-1))) ? 1 : -1;
            state++;
        }
    } else {
        int j=0;
        for (int i=0; i<dom->vectorsize && j<k; i++) {
            if (i != proj[j]) continue;
            const int sb = dom->statebits[i];
            for (int n=0; n<sb; n++) *arr++ = (*state & (1LL<<(sb-n-1))) ? 1 : 0;
            state++;
            j++;
        }
    }
	 *
	 */

	/* My own re-writeup of Sylvan's state_to_cube method	 */
	if (k == -1) {
		int sb;
		int i_arr = 0;
		int i_state = 0;
		for (int i=0; i<dom->vectorsize; i++) {
			sb = dom->statebits[i];
			for (int n=0; n<sb; n++) {
				arr[i_arr] = ( state[i_state] & (1 << (n)) ) ? 1 : 0;
				i_arr++;
			}
			i_state++;
		}
	}
	else {
		int j=0;
		int sb;
		int i_arr = 0; // index in arr
		for (int i=0; i<dom->vectorsize && j<k; i++) {
			if (i == proj[j]) {
				sb = dom->statebits[i];
				for (int n=0; n<sb; n++) {
					arr[i_arr] = (state[j] & (1 << (sb-n-1))) ? 1 : 0;
					i_arr++;
				}
				j++;
			}
		}
	}
}

// Adds the state vector e to the set
// e has length dom->vectorsize and each 4-byte integer contains xstatebits bits
static void set_add(vset_t set, const int* e) {
//	printf("[Sdd set add] set %u k=%i.\n", set->id, set->k);
	//printf("  k: %i\n", set->k);
	if (set->k == -1) {
		// ???
		uint8_t cube[set->dom->vectorsize * xstatebits];
		state_to_cube(set->dom, set->k, set->proj, e, cube);
		set->sdd = sdd_disjoin(set->sdd, sdd_getCube(set->state_variables, cube, set->nstate_variables), sisyphus);
	}
	else {
        // e is a full state vector, but this set only "cares" about a subset of the variables.
		// Collect the relevant variables into f
        int f[set->k];
        for (int i=0, j=0; i<set->dom->vectorsize && j<set->k; i++) {
            if (i == set->proj[j]) {
            	f[j++] = e[i];
            }
        }
        // cube is an array of 16*k bits
        uint8_t cube[set->k * xstatebits];
        state_to_cube(set->dom, set->k, set->proj, f, cube);
        set->sdd = sdd_disjoin(set->sdd, sdd_getCube(set->state_variables, cube, set->nstate_variables), sisyphus);
	}
}

static int set_member(vset_t set, const int* e) {
//	printf("[Sdd set member] set %u.\n", set->id);
	SddNode* elem = sdd_manager_true(sisyphus);
	vset_ll_t set_ll = get_vset(set->id);
	if (set_ll->k == -1) {
		for (int i=0; i<set->dom->vectorsize; i++) {
			for (int b=0; b<xstatebits; b++) {
				elem = sdd_conjoin(elem, getLiteral(xstatebits * i + b + 1, (e[i] & (1 << b)) ? 1 : 0, 0), sisyphus);
			}
		}
	}
	else {
		for (int i=0; i<set_ll->k; i++) {
			for (int b=0; b<xstatebits; b++) {
				elem = sdd_conjoin(elem, getLiteral(xstatebits * set_ll->proj[i] + b + 1, (e[i] & (1<<b)) ? 1 : 0, 0), sisyphus);
			}
		}
	}
	elem = sdd_conjoin(elem, set->sdd, sisyphus);
	return sdd_node_is_false(elem);
}

static int set_is_empty(vset_t set) {
	//printf("[Sdd set is empty] set %u ", set->id);
	/*
	if (sdd_node_is_false(set->sdd)) {
		printf("(Yes)\n");
	}
	else {
		//SddModelCount mc = set_count_exact(set);
		//printf("(No, %llu models: ", mc);
		//small_enum(set);
		//printf(")\n");
	}
	*/
	printf("Memory footprint: %lu  |  %lu\n", sdd_manager_size(sisyphus), sdd_manager_count(sisyphus));
	return sdd_node_is_false(set->sdd) ? 1 : 0;
}

static int set_equal(vset_t set1, vset_t set2) {
//	printf("[Sdd set equal] set %u == set %u?\n", set1->id, set2->id);
	return set1->sdd == set2->sdd;
}

static void set_clear(vset_t set) {
//	printf("[Sdd set clear] set %u := (empty)\n", set->id);
	set->sdd = sdd_manager_false(sisyphus);
	//printf("  [Sdd set clear] Cleared set.\n");
}

static void set_copy(vset_t dst, vset_t src) {
	//printf("[Sdd set copy] set %u := set %u (mc = %llu)", dst->id, src->id, set_count_exact(src));
	//small_enum(src); printf("\n");
	dst->sdd = src->sdd;

	// Save the fact that dst is now defined over the variables of src
	vset_set_domain(dst, src);
}

static void set_enum(vset_t set, vset_element_cb cb, void* context) {
	SddModelCount mc = set_count_exact(set);
	printf("  [Sdd enum] set %u (%llu models)\n", set->id, mc);
	if (sdd_node_is_false(set->sdd)) {
		printf("    (empty)\n");
	}
	else {
		SddModelCount i = 0;
		struct sdd_mit_master mas;
		for (mas = sdd_get_iterator(set); mas.finished == 0; sdd_next_model(&mas)) {
			printf("    ");
			for (int i=0; i<set->dom->vectorsize * xstatebits; i++) {
				if ((i%16) == 0 && i != 0) {
					printf(" ");
				}
				printf("%u", mas.e[i]);
			}
			printf("\n");
			i++;
			if (i > mc) {
				printf("  \n\nWell that's curious. We got more elements than we counted models.\n");
				fflush(stdout);
				getchar();
			}
		}
		if (i < mc) {
			printf("\n\nWell that's curious. We got less elements than we counted models.\n"); fflush(stdout);
			getchar();
		}
	}
}

static void set_update(vset_t dst, vset_t src, vset_update_cb cb, void* context) {
//	printf("[Sdd set update]\n");
}

static void set_example(vset_t set, int* e) {
//	printf("[Sdd set example]\n");
}

static void set_count(vset_t set, long* nodes, double* elements) {
//	printf("[Sdd set count] set %u\n", set->id);
	if (nodes != NULL) {
		*nodes = sdd_count(set->sdd);
	}
	if (elements != NULL) {
		SddModelCount mc = set_count_exact(set);
	//	printf("  [Sdd set count] Set contains %llu elements.\n", mc);
		*elements = (double) mc;
	}
}

static void rel_count(vrel_t set, long* nodes, double* elements) {
//	printf("[Sdd rel count]rel %u\n", set->id);
	if (nodes != NULL) {
		*nodes = sdd_count(set->sdd);
	}
	if (elements != NULL) {
		*elements = (double) sdd_model_count(set->sdd, sisyphus);
	}
}

static void set_union(vset_t dst, vset_t src) {
	static unsigned int ncalls = 0; ncalls++;
//	printf("[Sdd set union %u]: %u := %u + %u  (mc = %llu vs %llu) (k=%i vs %i)\n", ncalls, dst->id, dst->id, src->id,
//			set_count_exact(src), set_count_exact(dst), src->k, dst->k);
	SddNode* dstSdd = dst->sdd;
	if (sdd_node_is_false(dst->sdd)) {
//		printf("  [Sdd set union] dst is empty.\n");
		dst->sdd = src->sdd;
		//printf("  [Sdd set union] But not anymore! %llu\n", sdd_model_count(dst->sdd, sisyphus));
		//printf("  [Sdd set union] Because src %u had %llu.\n", sdd_model_count(src->sdd, sisyphus));
	}
	else if (sdd_node_is_false(src->sdd)) {
//		printf("  [Sdd set union] src is empty.\n");
		// Do nothing.
	}
	else {
		if (vset_domains_are_disjoint(dst, src)) {
			dst->sdd = sdd_conjoin(dst->sdd, src->sdd, sisyphus);
//			printf("  [Sdd set union] Uh oh, we should probably write down that the domain has changed.\n");
			vset_add_to_domain(dst, src);
		}
		else {
//			printf("  [Sdd set union] Computations tells us the vset domains are not disjoint:\n");
//			vset_exposition(src);
//			vset_exposition(dst);
			SddNode* dstSdd = dst->sdd;
			SddNode* sdd_union = sdd_disjoin(dst->sdd, src->sdd, sisyphus);
			SddModelCount srcmc = set_count_exact(src);
			SddModelCount dstmc = set_count_exact(dst);
			dst->sdd = sdd_union;
			SddModelCount unionmc = set_count_exact(dst);
			if (unionmc > srcmc + dstmc) {
				printf("  [Sdd union] something fishy going on here, %llu cup %llu = %llu.\n", srcmc, dstmc, unionmc);
				dst->sdd = dstSdd;
				set_enum(dst, 0, 0);
				set_enum(src, 0, 0);
				dst->sdd = sdd_union;
				set_enum(dst, 0, 0);
				sdd_save_as_dot("src.dot", src->sdd);
				sdd_save_as_dot("dst.dot", dst->sdd);
				sdd_save_as_dot("union.dot", sdd_union);

				fflush(stdout);
				getchar();
			}
			else {
				dst->sdd = sdd_union;
			}
		}
	}
}

static void set_minus(vset_t dst, vset_t src) {
//	printf("[Sdd set minus] set %u := %u \\ %u   (mc %u = %llu,  mc %u = %llu)\n", dst->id, dst->id, src->id, dst->id, set_count_exact(dst), src->id, set_count_exact(src));
	if (dst->sdd != src->sdd) {
		dst->sdd = sdd_conjoin(dst->sdd, sdd_negate(src->sdd, sisyphus), sisyphus);
		//printf("  [Sdd set minus] now &(%u->sdd) = %p\n", dst->id, dst->sdd);
	}
	else {
		dst->sdd = sdd_manager_false(sisyphus);
//		printf("  [Sdd set minus] Sdds were equal, so %u := False (@%p)\n", dst->id, dst->sdd);
	}
}

static void set_intersect(vset_t dst, vset_t src) {
//	printf("[set intersect] set %u := %u /\\ %u.\n", dst->id, dst->id, src->id);
	if (dst->sdd != src->sdd) {
		dst->sdd = sdd_conjoin(dst->sdd, src->sdd, sisyphus);
	}
	//printf("  [set intersect] now mc = %u", (unsigned int) sdd_model_count(dst->sdd, sisyphus));
}

static void set_next(vset_t dst, vset_t src, vrel_t rel) {
	static unsigned int ncalls = 0; ncalls++;
/*
	printf("[Sdd set next %u]   %u := rel %u (*) set %u.\n", ncalls, dst->id, rel->id, src->id);
	SddModelCount mcSrc = sdd_model_count(src->sdd, sisyphus);
	SddModelCount mcDst = sdd_model_count(dst->sdd, sisyphus);
	SddModelCount mcRel = sdd_model_count(rel->sdd, sisyphus);
	printf("  [Sdd set next]  #src=%llu #dst=%llu #rel=%llu\n", mcSrc, mcDst, mcRel);
*/
	if (sdd_node_is_false(rel->sdd)) {
//		printf("  [Sdd set next]  Rel has no models, so exiting.\n");
		dst->sdd = sdd_manager_false(sisyphus);
		return;
	}

	//printf("  [Sdd set next] Conjoining...\n");
	SddNode* conj = sdd_conjoin(src->sdd, rel->sdd, sisyphus);
//	mcSrc = sdd_model_count(conj, sisyphus);
//	printf("  [Sdd set next]  Conjoined! #conj=%llu\n", mcSrc);
	if (sdd_node_is_false(conj)) {
//		printf("  [Sdd set next] No transitions, so exit.\n");
		dst->sdd = sdd_manager_false(sisyphus);
		return;
	}

	int n = sdd_manager_var_count(sisyphus);
	int* exists_map = malloc(sizeof(int) * (n + 1)); // TODO free
	// Initialise map to zero
	for (int i=0; i <= n; i++) {
		exists_map[i] = 0;
	}
	// Mark variables read by rel
	vrel_ll_t rel_ll = get_vrel(rel->id);
	//printf("  [Sdd set next]  Quantifying %i read variables:", rel_ll->r_k);
	unsigned int sdd_var;
	for (int v=0; v<rel_ll->r_k; v++) {
		//printf(" %i:", rel_ll->r_proj[v]);
		for (int i=0; i<xstatebits; i++) {
			sdd_var = 2*(xstatebits*rel_ll->r_proj[v] + i)+1;
			//printf(" %u", sdd_var);
			exists_map[sdd_var] = 1;
		}
	}
	//printf("\n  [Sdd set next]  Quantifying %i write variables.\n", rel_ll->w_k);
	// Mark variables written by rel
	for (int v=0; v<rel_ll->w_k; v++) {
		for (int i=0; i<xstatebits; i++) {
			sdd_var = 2*(xstatebits*rel_ll->w_proj[v] + i)+1;
			exists_map[sdd_var] = 1;
		}
	}
/*
	printf("  [Sdd set next]  Exists map: ");
	for (int i=0; i <= n; i++) {
		printf("%i", exists_map[i]);
		if (i % 16 == 0) printf(" ");
	}
	printf("\n");
*/
	//printf("  [Sdd set next]  Existing..."); //prompt();
	/*
	for (SddLiteral v = 1; v <= n; v += 2) {
		printf("  [Sdd next set] Existing var %lu...\n", v);
		dst->sdd = sdd_exists(v, dst->sdd, sisyphus);
		printf("  [Sdd set next] Existed!\n");
	}
	 *
	 */
	SddNode* existed = sdd_exists_multiple(exists_map, conj, sisyphus);
//	mcSrc = sdd_model_count(existed, sisyphus);
	if (sdd_node_is_false(existed)) {
//		printf("  [Sdd set next]  Existed. No models. Exit.\n");
		dst->sdd = existed;
		return;
	}
//	printf("  Existed! #conj=%llu\n  [Sdd set next] Renaming...", mcSrc);

	// Rename the primed variables to unprimed variables
	SddLiteral* var_map = malloc(sizeof(SddLiteral) * (n + 1)); // TODO free
	for (int i=0; i<=n; i++) {
		var_map[i] = i;
	}
	for (int v=0; v<rel_ll->r_k; v++) {
		for (int i=0; i<xstatebits; i++) {
			sdd_var = 2*(xstatebits*rel_ll->r_proj[v]+i) + 2;
			var_map[sdd_var] = sdd_var-1;
		}
	}
	for (int v=0; v<rel_ll->w_k; v++) {
		for (int i=0; i<xstatebits; i++) {
			sdd_var = 2*(xstatebits*rel_ll->w_proj[v]+i) + 2;
			var_map[sdd_var] = sdd_var - 1;
		}
	}
/*
	printf("  [Sdd set next] Rename map: ");
	for (int v=0; v<=n; v++) {
		printf(" (%i %li)", v, var_map[v]);
		if (v%16 == 0) printf("  ");
	}
	printf("\n");
*/

	// Diagnostics
	/* On input Rel 2 (*) Set 15
	 * With rel 2 = {(*0,*1)},
	 * The conjunction goes well, but then the renaming goes astray, and loses all its models,
	 *   at least according to set_enum.
	 *   The thing is that set_enum conjoins a set with setting all primes to 0,
	 *   so probably something in the renaming leaves the primed variables of set 15 alive,
	 *   and somehow fails to rename them to unprimed variables.
	 *   But why only for set 15?
	 */

	SddNode* renamed = sdd_rename_variables(existed, var_map, sisyphus);
	dst->sdd = renamed;
	SddNode* renamedZero = sdd_conjoin(renamed, sdd_primes_zero(), sisyphus);
//	printf("  [Sdd set next]  Renamed! #conj = %llu. Here it is.\n", mcSrc);
	if (sdd_node_is_false(renamedZero)) {
		sdd_save_as_dot("relatio.dot", rel->sdd);
		sdd_save_as_dot("reached.dot", src->sdd);
		sdd_save_as_dot("conjunc.dot", conj);
		sdd_save_as_dot("renamed.dot", renamed);
		sdd_save_as_dot("existed.dot", existed);
		printf("  [Sdd set next]  No models left after renaming. Very strange. See 'renamed.dot' and 'conjunc.dot'.\n");
		fflush(stdout);
		getchar();
		return;
	}

	//vset_exposition(dst);

	//set_enum(dst, 0, 0);
}

static void set_prev(vset_t dst, vset_t src, vrel_t rel, vset_t univ) {
	printf("[Sdd] prev.\n");
	// TODO
}

static void set_project(vset_t dst, vset_t src) {
	static unsigned int ncalls = 0; ncalls++;
//	printf("[Sdd project %u] set %u := set %u (mc = %llu) ", ncalls, dst->id, src->id, set_count_exact(src));
	//small_enum(src); printf("\n");
	if (!vset_domains_are_equal(dst, src)) {
		if (src->k == -1) {
//			printf("  [Sdd project] src->k = -1, nsv=%u so existing away.\n", dst->nstate_variables);
			//printf("  [Sdd project] Before quantifying, dst is: \n");
			//set_enum(dst, 0, 0);
			//printf("  [Sdd project] Before quantifying, src is:\n");
			//set_enum(src, 0, 0);
			// Exists!
			int* exists_map = malloc((sdd_manager_var_count(sisyphus)+1) * sizeof(int)); // freed
			exists_map[0] = 0;
			// Set the primed variables to non-quantified
			for (int v=0; v<sdd_manager_var_count(sisyphus)/2; v++) {
				exists_map[2*v+2] = 0;
			}
			//printf("  [Sdd project] Quantify primed variables: No.\n");
			// Quantify away any state variables that do not appear in this set
			int var=0;
//			printf("  ");
			for (unsigned int i=0; i<dst->nstate_variables; i++) {
//				printf(" %i=%i", i, dst->state_variables[i]);
				while (var < dst->state_variables[i]) {
					exists_map[var+1] = 1;
					var += 2;
				}
				exists_map[var+1] = 0;
				var += 2;
			}
//			printf("\n");
			//printf("  [Sdd project] Did the skipping part.\n");
			while (var < sdd_manager_var_count(sisyphus)) {
				exists_map[var+1] = 1;
				var += 2;
			}
/*
			printf("  [Sdd project] Exists map: ");
			for (int v=0; v <= sdd_manager_var_count(sisyphus); v++) {
				if (v % 16 == 1) printf(" ");
				printf("%i", exists_map[v]);
			}
			printf("\n");
*/
			//printf("\n  [Sdd project] Quantifying the variables...\n");
			SddNode* proj = sdd_exists_multiple(exists_map, src->sdd, sisyphus);
			dst->sdd = proj;
			free(exists_map);

			// Save the fact that dst is now defined over the variables of src
			// Actually, don't do that
			//vset_set_domain(dst, src);

			//printf("  [Sdd project] Ended up with this set:\n");
			//set_enum(dst, 0, 0);
		}
		else {
			// ???
			printf("  [Sdd project] ERRORR HELP I don't know what to do; src and dst defined over different variables!\n");
			vset_exposition(src);
			vset_exposition(dst);
		}
	}
	else {
		dst->sdd = src->sdd;
	}
}

static void set_zip(vset_t dst, vset_t src) {
	printf("[Sdd] Set zip.\n");
	// TODO
}

static void rel_add_act(vrel_t rel, const int* src, const int* dst, const int* cpy, const int act) {
	printf("[Sdd rel add action]\n");
}

static void rel_add_cpy(vrel_t rel, const int* src, const int* dst, const int* cpy) {
//	printf("[Sdd rel add copy] Relation %u add ", rel->id);
	vrel_ll_t rel_ll = get_vrel(rel->id);
/*
	for (int i=0; i<rel_ll->r_k; i++) {
		printf("%i ", src[i]);
	}
	printf(" -->  ");
	for (int i=0; i<rel_ll->w_k; i++) {
		printf("%i ", dst[i]);
	}
	printf("  cpy = ");
	for (int i=0; i<3; i++) {
		printf("%i ", cpy[i]);
	}
	printf("\n");
	fflush(stdout);
*/
	SddNode* srcSdd = sdd_manager_true(sisyphus);
	SddNode* dstSdd = sdd_manager_true(sisyphus);

	// Prepare srcSdd
	int sdd_var;
	for (int v=0; v<rel_ll->r_k; v++) {
//		printf("  [Sdd rel add copy] Read variable %i: %i\n", v, rel_ll->r_proj[v]);
		fflush(stdout);
		for (int i=0; i<xstatebits; i++) {
			sdd_var = xstatebits*rel_ll->r_proj[v] + i + 1;
			srcSdd = sdd_conjoin(srcSdd, getLiteral(sdd_var, src[v] & (1 << i), 0), sisyphus);
		}
	}
	if (rel_ll->r_k == -1) {
//		printf("  [Sdd rel add copy] r_k == -1.\n");
		for (int v=0; v<rel->dom->vectorsize; v++) {
			for (int i=0; i<xstatebits; i++) {
			srcSdd = sdd_conjoin(srcSdd, getLiteral(xstatebits*v+i+1, src[v] & (1 << i), 0), sisyphus);
			}
		}
	}
	// Prepare dstSdd
	for (int v=0; v<rel_ll->w_k; v++) {
//		printf("  [Sdd rel add copy] Write variable %i: %i\n", v, rel_ll->w_proj[v]);
//		fflush(stdout);
		for (int i=0; i<xstatebits; i++) {
			sdd_var = xstatebits*rel_ll->w_proj[v] + i + 1;
			dstSdd = sdd_conjoin(dstSdd, getLiteral(sdd_var, dst[v] & (1 << i), 1), sisyphus);
		}
	}
	int w = 0;
	for (int v=0; v<rel_ll->r_k; v++) {
		// Invariant: w_proj[w] >= r_proj[v]
		while (w < rel_ll->w_k && rel_ll->w_proj[w] < rel_ll->r_proj[v]) w++;
		if (w > rel_ll->w_k || rel_ll->w_proj[w] != rel_ll->r_proj[v]) {
			// Variable is read but not written, so cover it
			for (int i=0; i<xstatebits; i++) {
				sdd_var = xstatebits*rel_ll->r_proj[v] + i + 1;
				dstSdd = sdd_conjoin(dstSdd, getLiteral(sdd_var, src[v] & (1 << i), 1), sisyphus);
			}
		}
	}
	//printf("  [Sdd rel add copy] Finished src, dst in cases k != -1"); fflush(stdout);
	if (rel_ll->w_k == -1) {
		for (int v=0; v<rel->dom->vectorsize; v++) {
			for (int i=0; i<xstatebits; i++) {
				dstSdd = sdd_conjoin(dstSdd, getLiteral(xstatebits*v+i+1, dst[v] & (1 << i), 1), sisyphus);
			}
		}
	}

//	printf("  [Sdd rel add cpy] edge: %llu and %llu. ", sdd_model_count(srcSdd, sisyphus), sdd_model_count(dstSdd, sisyphus));
	SddNode* src_and_dst = sdd_conjoin(srcSdd, dstSdd, sisyphus);
//	printf("Ok. |.|=%llu. Add: ", sdd_model_count(src_and_dst, sisyphus));
	rel->sdd = sdd_disjoin(rel->sdd, src_and_dst, sisyphus);
//	printf("Ok.\n"); //[Sdd rel add cpy] Now rel has %llu models.\n", sdd_model_count(rel->sdd, sisyphus));
}

static void rel_add(vrel_t rel, const int* src, const int* dst) {
	printf("[Sdd rel add]\n");
	rel_add_cpy(rel, src, dst, 0);
}

SddLiteral vtree_highest_var(Vtree* tree) {
	if (tree == 0) return 0;
	else if (sdd_vtree_is_leaf(tree)) {
		SddLiteral v = sdd_vtree_var(tree);
		if (v % 2 == 0) return 0;
		else return (((unsigned int)v)-1) / 2;
	}
	else {
		SddLiteral s, p;
		s = vtree_highest_var(sdd_vtree_left(tree));
		p = vtree_highest_var(sdd_vtree_right(tree));
		return s > p ? s : p;
	}
}

/* Returns the normalised id of the lowest unprimed variable below tree
 */
SddLiteral vtree_lowest_var(Vtree* tree) {
	if (tree == 0) return 0;
	else if (sdd_vtree_is_leaf(tree)) {
		SddLiteral v = sdd_vtree_var(tree);
		if (v % 2 == 0) return -1;
		else return (v-1) / 2;
	}
	else {
		SddLiteral s, p;
		s = vtree_lowest_var(sdd_vtree_left(tree));
		p = vtree_lowest_var(sdd_vtree_right(tree));
		if (s == -1 || p == -1) return (s > p ? s : p);
		return s < p ? s : p;
	}
}

void sdd_mit_skip_false_prime(struct sdd_model_iterator* it) {
	if (it->root != 0 && sdd_node_is_decision(it->root) && it->i < sdd_node_size(it->root)) {
		SddNode* prime = sdd_node_elements(it->root)[2*(it->i)+1];
		if (sdd_node_is_false(prime)) {
			//printf("    [Sdd skip false] Skipping False prime.\n");
			it->i++;
		}
	}
}

unsigned int vset_uses_var(vset_t set, SddLiteral var) {
	if (var % 2 == 0) return 0;
	vset_ll_t vset_ll = get_vset(set->id);
	if (vset_ll-> k == -1) {
		return 1;
	}
	unsigned int var_norm = (var - 1) / 2;
	for (int i=0; i<vset_ll->k; i++) {
		if (var_norm >= (unsigned int) xstatebits * vset_ll->proj[i] && var_norm < (unsigned int) xstatebits * (vset_ll->proj[i]+1)) {
			return 1;
		}
	}
	return 0;
}

/* Version 3.0
 */
void sdd_mit_init_prime(struct sdd_mit_master* mas, Vtree* tree) {
	if (tree == 0 || sdd_vtree_is_leaf(tree)) return; // There is no prime to initialise
	struct sdd_model_iterator* it = &(mas->nodes[sdd_vtree_position(tree)]);

	Vtree* root_tree = (it->root == 0) ? 0 : sdd_vtree_of(it->root);
	Vtree* right_tree = sdd_vtree_right(tree);
	if (it->root == 0) {
		//printf("  [mit init prime] root == 0.\n"); fflush(stdout);
		sdd_get_iterator_rec(mas, 0, right_tree);
	} else if (root_tree == tree) {
		//printf("  [mit init prime] root normalised to this Vtree.\n"); fflush(stdout);
		SddNode* prime = sdd_node_elements(it->root)[2*(it->i)+1];
		if (prime == sdd_manager_true(sisyphus)) {
			sdd_get_iterator_rec(mas, 0, right_tree);
		}
		else {
			sdd_get_iterator_rec(mas, prime, right_tree);
		} // TODO maybe pass True node as prime? Would be cleaner
	} else if (sdd_vtree_is_sub(root_tree, right_tree)) {// Is the root normalised to the left tree?
		//printf("  [mit init prime] root normalised to right Vtree.\n"); fflush(stdout);
		sdd_get_iterator_rec(mas, it->root, right_tree);
	} else {
		//printf("  [mit init prime] root normalised to left, so passing null root to the right.\n");
		sdd_get_iterator_rec(mas, 0, right_tree);
	}
}

/* Version 3.0
 */
void sdd_mit_init_sub(struct sdd_mit_master* mas, Vtree* tree) {
	if (tree == 0 || sdd_vtree_is_leaf(tree)) return; // There is no sub to initialise
	struct sdd_model_iterator* it = &(mas->nodes[sdd_vtree_position(tree)]);
	Vtree* root_tree = (it->root == 0) ? 0 : sdd_vtree_of(it->root);
	Vtree* left_tree = sdd_vtree_left(tree);
	if (it->root == 0) {
		sdd_get_iterator_rec(mas, 0, left_tree);
	} else if (root_tree == tree) {
		sdd_get_iterator_rec(mas, sdd_node_elements(it->root)[2*(it->i)], left_tree);
	} else if (sdd_vtree_is_sub(root_tree, left_tree)) {
		sdd_get_iterator_rec(mas, it->root, left_tree);
	} else {
		sdd_get_iterator_rec(mas, 0, left_tree);
	}
}

/* Version 3.0
 */
void sdd_get_iterator_rec(struct sdd_mit_master* mas, SddNode* root, Vtree* tree) {
	struct sdd_model_iterator* it = &(mas->nodes[sdd_vtree_position(tree)]);
	it->root = root;
	it->i = 0;
	it->finished = 0;
	it->var_is_used = 0;
	sdd_mit_skip_false_prime(it);

	if (sdd_vtree_is_leaf(tree)) {
		SddLiteral var = sdd_vtree_var(tree);
		if (it->root != 0) {
			it->i = sdd_node_literal(it->root) > 0 ? 1 : 0;
			it->var_is_used = 1;
		}
		else {
			it->var_is_used = vset_uses_var(mas->vset, var);
		}
		if (it->var_is_used) {
			mas->e[(var-1)/2] = it->i;
			//printf("    [get iterator]  e[%u] := %u\n", (var-1)/2, it->i);
		}
	}
	else {
		sdd_mit_init_prime(mas, tree);
		sdd_mit_init_sub(mas, tree);
	}
}

struct sdd_mit_master sdd_get_iterator(vset_t set) {
	struct sdd_mit_master mas;
	mas.vset = set;
	mas. e = (int*) malloc(sizeof(int) * set->dom->totalbits);
	for (int i=0; i<set->dom->totalbits; i++) {
		mas.e[i] = 0;
	}
	mas.finished = 0;
	mas.nodes = (struct sdd_model_iterator*) malloc(sizeof(struct sdd_model_iterator) * 2*sdd_manager_var_count(sisyphus));
	sdd_get_iterator_rec(&mas, set->sdd, sdd_manager_vtree(sisyphus));
	return mas;
}

/* Version 3.0
 */
void sdd_model_restart(struct sdd_mit_master* mas, Vtree* tree) {
	struct sdd_model_iterator* it = &(mas->nodes[sdd_vtree_position(tree)]);
	sdd_get_iterator_rec(mas, it->root, tree);
	/*
	it->finished = 0;
	// it->i = 0; // TODO uncomment this

	if (sdd_vtree_is_leaf(tree)) {
		if (it->root == 0) {
			it->i = 0;
		} else {
			it->i = (sdd_node_literal(it->root) > 0) ? 1 : 0;
		}
		if (it->var_is_used) {
			SddLiteral var = sdd_vtree_var(tree);
			unsigned int var_norm = (var-1) / 2;
			mas->e[var_norm] = it->i;
		}
	}
	else {
		if (it->root != 0 && sdd_vtree_of(it->root) == tree) {
			it->i = 0;
		}
		//sdd_model_restart(mas, sdd_vtree_left(tree));
		//sdd_model_restart(mas, sdd_vtree_right(tree));
	}
	*/
}

/* Version 3.0
 */
void sdd_mit_free(struct sdd_mit_master mas) {
	free(mas.e);
	free(mas.nodes);
}

/* Version 3.0 Next model
 * Algorithm description:
	 * In case of non-leaf:
	 * Try to get another prime model
	 *   If that succeeds, exit.
	 * Otherwise, try to get another sub model
	 *   If that succeeds, reset the prime and exit.
	 *   Otherwise, go to the next element of this decision node, it->i++
	 *   If prime == False, then go to the next element again, it->i++
	 *   If this element exists, then
	 *     Set the sub, prime accordingly, again.
	 *   Otherwise, indicate it->finished = 1 that there are no more models here.
 */
void sdd_next_model_rec(struct sdd_mit_master* mas, Vtree* tree) {
	SddLiteral treeid = sdd_vtree_position(tree);
	struct sdd_model_iterator* it = &(mas->nodes[treeid]);
	if (it->finished == 1) return;
	if (sdd_vtree_is_leaf(tree)) {
		SddLiteral var_sdd = sdd_vtree_var(tree);
		SddLiteral var = (var_sdd - 1) / 2;
		if (it->root != 0) {
			//printf("  [Sdd next model]  Leaf (var %li) is fixed\n", var);
			it->finished = 1;
		}
		else if (var_sdd % 2 == 0) {
			//printf("  [Sdd next model]  Leaf var %li prime\n", var);
			it->finished = 1;
		}
		else if (it->var_is_used && it->i == 0) {
			//printf("  [Sdd next model]  Leaf;  e[%lu] := 1\n", var); fflush(stdout);
			it->i++;
			mas->e[var] = 1;
		}
		else {
			//printf("  [Sdd next model]  Leaf (var %li) finished\n", sdd_vtree_var(tree));fflush(stdout);
			it->finished = 1;
		}
		return;
	}
	SddLiteral tree_hi = vtree_highest_var(tree);
	SddLiteral tree_lo = vtree_lowest_var(tree);
	if (it->root != 0 && sdd_node_is_decision(it->root) && sdd_vtree_of(it->root) == tree) {
		//printf("  [Sdd next model] Node %li|%li  :  %u / %u\n", tree_lo, tree_hi, it->i, sdd_node_size(it->root));
	}
	else {
		//printf("  [Sdd next model] Node %li|%li\n", tree_lo, tree_hi);
	}
	sdd_next_model_rec(mas, sdd_vtree_right(tree));
	SddLiteral primeid = sdd_vtree_position(sdd_vtree_right(tree));
	SddLiteral subid   = sdd_vtree_position(sdd_vtree_left(tree));
	if (mas->nodes[primeid].finished == 1) {
		//printf("  [Sdd next model]  Node %li|%li's prime is finished. Trying next sub model.\n", tree_lo, tree_hi);
		sdd_next_model_rec(mas, sdd_vtree_left(tree));
		if (mas->nodes[subid].finished == 0) {
			//printf("  [Sdd next model]  Node %li|%li's sub worked. restarting prime.\n", tree_lo, tree_hi); fflush(stdout);
			sdd_model_restart(mas, sdd_vtree_right(tree));
		}
		else if (it->root != 0 && sdd_vtree_of(it->root) == tree) {
			it->i++;
			sdd_mit_skip_false_prime(it);
			//printf("  [Sdd next model]  Node %li|%li's sub oom. Starting next sub: %u / %u.\n", tree_lo, tree_hi, it->i, sdd_node_size(it->root)); fflush(stdout);
			if (it->i < sdd_node_size(it->root)) {
				//printf("  [Sdd next model]  Node %li|%li Moved to next element.\n", tree_lo, tree_hi); fflush(stdout);
				sdd_mit_init_prime(mas, tree);
				//printf("  [Sdd next model]  Node %li|%li Initialised prime.\n", tree_lo, tree_hi); fflush(stdout);
				sdd_mit_init_sub(mas, tree);
				//printf("  [Sdd next model]  Node %li|%li Initialised sub.\n", tree_lo, tree_hi); fflush(stdout);
			}
			else {
				//printf("  [Sdd next model]  Node %li|%li's sub oom. That was the last sub. Finished.\n", tree_lo, tree_hi); fflush(stdout);
				it->finished = 1;
			}
		}
		else {
			//printf("  [Sdd next model]  Node %li|%li is not decision, and oom. Finished.\n", tree_lo, tree_hi);
			it->finished = 1;
		}
	}
}

/* Version 3.0
 */
void sdd_next_model(struct sdd_mit_master* mas) {
	sdd_next_model_rec(mas, sdd_manager_vtree(sisyphus));
	mas->finished = mas->nodes[sdd_vtree_position(sdd_manager_vtree(sisyphus))].finished;
}

// A short set enumerator for sets with 1 variable
void small_enum(vset_t src) {
	printf("{"); fflush(stdout);
	if (sdd_node_is_false(src->sdd)) {
		printf(" }");
		return;
	}
	// print in blocks of 5x5
	SddModelCount mc = set_count_exact(src);
	if (mc > 5) {
		printf("\n    ");
	}
	SddModelCount n = 0;
	unsigned int x;
	vset_ll_t src_ll = get_vset(src->id);
	unsigned int k = (src_ll->k == -1 ) ? src->dom->vectorsize : src_ll->k;
	struct sdd_mit_master mas;
	for (mas = sdd_get_iterator(src); mas.finished == 0; sdd_next_model(&mas)) {
		n++;
		printf("    set_e(e,");
		for (unsigned int i=0; i<k; i++) {
			x = 0;
			for (int b=0; b<xstatebits; b++) {
				x |= (mas.e[i*xstatebits + b]) << b;
			}
			printf("%u", x); fflush(stdout);
			if (i + 1 < k) {
				printf(",");
			}
		}
		printf(")\n    ");
	}
	printf(" }");
	if (n != mc) {
		printf("\n\n  That's strange. Enumerated %llu models out of %llu.\n", n, mc);
		sdd_save_as_dot("small_enum_error.dot", src->sdd);
		fflush(stdout);
		enum_error = 1;
	}
}

/* src and dst are arrays of integer values
 */
static void rel_update(vrel_t dst, vset_t src, vrel_update_cb cb, void* context) {
	static unsigned int ncalls = 0; ncalls++;
	SddModelCount src_mc = set_count_exact(src);
//	printf("[Sdd rel update %u] src = set %u (# = %llu), k=%i rel=%u\n", ncalls, src->id, src_mc, src->k, dst->id);	fflush(stdout);
//	vrel_exposition(dst);
	if (sdd_node_is_false(src->sdd)) {
//		printf("  [Sdd rel update] Source has no models. Abort.\n");
		return;
	}
	if (dst != 0 && dst->sdd == 0) {
		printf("[rel update] ERROR    dst->sdd == 0! :-( &dst == %p\n", dst->sdd);
		dst->sdd = sdd_manager_false(sisyphus); // This is a dirty quick fix. Why is sdd == 0? Fix that
	}
	else if (dst == 0) {
		printf("[rel update] ERROR    dst == 0! :-(\n");
	}
	//printf("  [rel update] set %u = ", src->id); small_enum(src);
	//printf("\n");
	vrel_ll_t rel_ll = get_vrel(dst->id);
	SddNode* root = src->sdd;
	int* e = malloc(sizeof(int) * rel_ll->r_k);
	// For each model of src
	//     Call the callback to find the new states
	//     Add the new states to dst
	if (sdd_node_is_decision(root)) {
		//printf("  [rel update] Node is decision.\n");
		struct sdd_mit_master mas;
		for (mas = sdd_get_iterator(src); mas.finished == 0; sdd_next_model(&mas)) {
			//printf("  [rel update] Another model: ");
			for (int i=0; i<src->dom->vectorsize * xstatebits; i++) {
				//if (i % 16 == 0) printf(" ");
				//printf("%u", it->e[i] ? 1 : 0);
			}
			//printf("\n");
			// Refactor mas.e to a bit-array
			for (int i=0; i<rel_ll->r_k; i++) {
				e[i] = 0;
			}
			int d;
			for (int i=0; i<rel_ll->r_k; i++) {
				for (int b=0; b<xstatebits; b++) {
					d = (mas.e[xstatebits*(rel_ll->r_proj[i])+b]) << b;
					//printf("  e[%i] |= %i\n", i, d);
					e[i] |= d;
				}
			}
			/* -- Failed hypothesis: pass full state vector to cb
			for (int i=0; i<src->dom->vectorsize; i++) {
				for (int b=0; b<xstatebits; b++) {
					d = (it->e[xstatebits*i + b]) << b;
					e[i] |= d;
				}
			}
			 */
			//printf("  [rel update] e = ");
			for (int i=0; i<rel_ll->r_k; i++) {
			//	printf(" %i", e[i]);
			}
			//printf("\n");
			cb(dst, context, e);
			//printf("  [rel update] Did the callback. Now relation has %llu models.\n", sdd_model_count(dst->sdd, sisyphus));
			//scanf("%s", word);
		}
		sdd_mit_free(mas);
//		printf("  [rel update] End of models.\n");
		//sdd_mit_free(it); // TODO uncomment this to free the data structure
	}
	else if (sdd_node_is_false(root)) {
//		printf("  [rel update] Relation is False.\n");
		return;
	}
	else if (sdd_node_is_true(root)) {
		printf("  [rel update] Rel is True.\n");
		return; // Lots of satisfying assignments
	}
	else {
		printf("  [rel update] Node is literal. Skipping.\n");
		// Node is a literal. Let's not.
	}

}

static void set_least_fixpoint(vset_t dst, vset_t src, vrel_t _rels[], int rel_count) {
	printf("[Sdd least fixpoint]\n");
}

static void set_least_fixpoint_par(vset_t dst, vset_t src, vrel_t _rels[], int rel_count) {
	printf("[Sdd least fixpoint parallel]\n");
}

static void set_reorder() {
	// Nope
}

/* Indicates that our package distinguishes read operations from write operations
 */
static int separates_rw() {
	return 0;
}

static void dom_set_function_pointers(vdom_t dom) {
	printf("[Sdd]  Setting function pointers.\n");
	//   Sets
	dom->shared.set_create = set_create;
	dom->shared.set_destroy = set_destroy;
	dom->shared.set_add = set_add;
	dom->shared.set_update = set_update;
	dom->shared.set_member = set_member;
	dom->shared.set_is_empty = set_is_empty;
	dom->shared.set_equal = set_equal;
	dom->shared.set_clear = set_clear;
	dom->shared.set_enum = set_enum;
	//dom->shared.set_enum_match = set_enum_match
	dom->shared.set_copy = set_copy;
	//dom->shared.set_copy_match
	dom->shared.set_example = set_example;
	dom->shared.set_union = set_union;
	dom->shared.set_intersect = set_intersect;
	dom->shared.set_minus = set_minus;
	dom->shared.set_zip = set_zip;
	dom->shared.set_project = set_project;
	dom->shared.set_count = set_count;

	//   Relations
	dom->shared.rel_create_rw = rel_create_rw;
	dom->shared.rel_add_act = rel_add_act;
	dom->shared.rel_add_cpy = rel_add_cpy;
	dom->shared.rel_add = rel_add;
	dom->shared.rel_update = rel_update;
	dom->shared.rel_count = rel_count;
	dom->shared.set_next = set_next;
	dom->shared.set_prev = set_prev;
	dom->shared.set_least_fixpoint = set_least_fixpoint;
	dom->shared.set_least_fixpoint_par = set_least_fixpoint_par;

	dom->shared.reorder = set_reorder;
	//dom->shared.set_dot = set_dot;
	//dom->shared.rel_dot = rel_dot;

	//dom->shared.dom_save = dom_save;
	//dom->shared.set_save = set_save;
	//dom->shared.set_load = set_load;
	//dom->shared.rel_save_proj = rel_save_proj;
	//dom->shared.rel_save = rel_save;
	//dom->shared.rel_load_proj = rel_load_proj;
	//dom->shared.rel_load = rel_load;
	dom->shared.rel_destroy = rel_destroy;

	dom->shared.separates_rw = separates_rw;
}

// initialise sisyphus Sdd Manager
void ltsmin_initialise_sdd(int vectorsize) {
	// Number of variables needed in Manager:
	// 2                 * vectorsize            * xstatebits
	// unprimed+primed     number of integer       bits per integer
	Vtree* left = sdd_vtree_new(2*vectorsize * xstatebits, "balanced");
	sisyphus = sdd_manager_new(left);
//	sisyphus = sdd_manager_create(2 * vectorsize * xstatebits, 0);
}

vdom_t dom_create(int vectorsize, int* _statebits, int actionbits) {
//	printf("[dom create]  Creating domain.\n");
	ltsmin_initialise_sdd(vectorsize);

	// Create the domain data structure
	vdom_t dom = (vdom_t) malloc(sizeof(struct vector_domain));
	vdom_init_shared(dom, vectorsize);
	dom_set_function_pointers(dom);

	// Initialize domain
	dom->vectorsize = vectorsize;
	dom->statebits = (int*) malloc(sizeof(int[vectorsize]));
	memcpy(dom->statebits, _statebits, sizeof(int[vectorsize]));
	dom->actionbits = actionbits;

	dom->totalbits = 0;
	for (int i=0; i<vectorsize; i++) {
		dom->totalbits += _statebits[i];
	}

	// Create state variables and prime variables
	dom->state_variables = malloc(sizeof(int[vectorsize * xstatebits]));
	dom->prime_variables = malloc(sizeof(int[vectorsize * xstatebits]));
	printf("  Allocated memory for state and prime variables.\n");
	int i_var = 0;
	uint32_t curvar = 0;
	for (int i=0; i<vectorsize; i++) {
		for (int j=0; j<_statebits[i]; j++) {
			dom->state_variables[i_var] = curvar;
			curvar++;
			dom->prime_variables[i_var] = curvar;
			i_var++;
			curvar ++;
		}
	}

	return dom;
}

vdom_t vdom_create_sdd(int n) {
//	printf("[vdom create sdd]  Creating domain! n = %i.\n", n);
	int _statebits[n];
	for (int i=0; i<n; i++) {
		_statebits[i] = xstatebits;
	}
	return dom_create(n, _statebits, 0);
}

#endif






