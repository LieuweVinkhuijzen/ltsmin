/*
 * vtree-utils.c
 *
 *  Created on: Oct 25, 2019
 *      Author: lieuwe
 */



// Every non-leaf vtree node has a unique dissection literal,
// and every literal is the dissection literal of a unique non-leaf vtree,
//   (except the last literal)
SddLiteral vtree_dissection_literal(Vtree* tree) {
//	printf("  Getting unique dissection literal of %li\n", sdd_vtree_position(tree)); fflush(stdout);
	if (sdd_vtree_is_leaf(tree)) {
		return sdd_vtree_var(tree);
	}
	return (sdd_vtree_position(tree) + 1) / 2;
//	return vtree_highest_var_nonprimed(sdd_vtree_left(tree));
}
