/*
 * latcalc.h -- umbrella header for the latcalc library.
 *
 * latcalc is an exact (arbitrary-precision, integer-only) calculation library
 * for base-60 arithmetic, fixed-scale arithmetic, residue "rod abacus"
 * arithmetic, the hexagonal lattice and modular dials.  It is the C companion
 * of the Lean library LatticeCalc; the headers name the Lean theorems that
 * state the mathematical facts each routine relies on.
 *
 * Link with -llatcalc -lm (or use pkg-config --libs latcalc).
 */
#ifndef LATCALC_H
#define LATCALC_H

#include "latcalc/common.h"
#include "latcalc/bigint.h"
#include "latcalc/rational.h"
#include "latcalc/sexa.h"
#include "latcalc/scaled.h"
#include "latcalc/rns.h"
#include "latcalc/eisenstein.h"
#include "latcalc/dial.h"
#include "latcalc/binrods.h"
#include "latcalc/ordersplit.h"
#include "latcalc/rodsieve.h"
#include "latcalc/abacus.h"

#endif /* LATCALC_H */
