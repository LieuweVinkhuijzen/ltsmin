/**
 * C wrapper for the C++ file ltl2spot.cpp
 */
#ifndef LTL2SPOT_H
#define LTL2SPOT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <ltsmin-lib/ltsmin-buchi.h>

void ltsmin_ltl2spot(ltsmin_expr_t e, int to_tgba);
ltsmin_buchi_t *ltsmin_hoa_buchi();

#ifdef __cplusplus
}
#endif

#endif // LTL2SPOT_H