/*
 * latcalc/common.h -- error codes and shared helpers.
 */
#ifndef LATCALC_COMMON_H
#define LATCALC_COMMON_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define LATCALC_VERSION_MAJOR 0
#define LATCALC_VERSION_MINOR 1
#define LATCALC_VERSION_PATCH 0
#define LATCALC_VERSION_STRING "0.1.0"

enum {
    LC_OK        =  0,
    LC_ENOMEM    = -1,  /* allocation failed */
    LC_EDIVZERO  = -2,  /* division by zero */
    LC_EPARSE    = -3,  /* malformed text input */
    LC_ERANGE    = -4,  /* value does not fit the requested C type */
    LC_EINEXACT  = -5,  /* the exact result is not representable in the requested form */
    LC_EDOMAIN   = -6,  /* argument outside the mathematical domain */
    LC_EINVAL    = -7   /* invalid argument (NULL, bad base, ...) */
};

/* Human-readable message for an error code. */
const char *lc_strerror(int code);

/* Library version string, e.g. "0.1.0". */
const char *lc_version(void);

/* Free memory returned by the library (strings, arrays). */
void lc_free(void *p);

#ifdef __cplusplus
}
#endif

#endif /* LATCALC_COMMON_H */
