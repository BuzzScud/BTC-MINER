/* latcalc -- error strings, version, memory. */
#include <stdlib.h>
#include "latcalc/common.h"

const char *lc_strerror(int code)
{
    switch (code) {
    case LC_OK:       return "ok";
    case LC_ENOMEM:   return "out of memory";
    case LC_EDIVZERO: return "division by zero";
    case LC_EPARSE:   return "malformed input";
    case LC_ERANGE:   return "value out of range for the requested type";
    case LC_EINEXACT: return "result not exactly representable in the requested form";
    case LC_EDOMAIN:  return "argument outside the domain";
    case LC_EINVAL:   return "invalid argument";
    default:          return "unknown error";
    }
}

const char *lc_version(void) { return LATCALC_VERSION_STRING; }

void lc_free(void *p) { free(p); }
