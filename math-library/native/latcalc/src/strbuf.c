/* latcalc -- internal growable string buffer. */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "strbuf.h"

void lc_sb_init(lc_strbuf *b) { b->s = NULL; b->len = 0; b->cap = 0; b->failed = 0; }

static int grow(lc_strbuf *b, size_t extra)
{
    if (b->failed) return 0;
    if (b->len + extra + 1 <= b->cap) return 1;
    size_t nc = b->cap ? b->cap : 32;
    while (nc < b->len + extra + 1) nc *= 2;
    char *p = realloc(b->s, nc);
    if (!p) { b->failed = 1; return 0; }
    b->s = p; b->cap = nc;
    return 1;
}

void lc_sb_putc(lc_strbuf *b, char c)
{
    if (!grow(b, 1)) return;
    b->s[b->len++] = c; b->s[b->len] = 0;
}

void lc_sb_puts(lc_strbuf *b, const char *s)
{
    size_t n = strlen(s);
    if (!grow(b, n)) return;
    memcpy(b->s + b->len, s, n + 1);
    b->len += n;
}

void lc_sb_printf(lc_strbuf *b, const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    if (n < 0 || !grow(b, (size_t)n)) { b->failed = 1; return; }
    va_start(ap, fmt);
    vsnprintf(b->s + b->len, (size_t)n + 1, fmt, ap);
    va_end(ap);
    b->len += (size_t)n;
}

char *lc_sb_finish(lc_strbuf *b)
{
    if (b->failed) { free(b->s); b->s = NULL; return NULL; }
    if (!b->s) { char *e = malloc(1); if (e) e[0] = 0; return e; }
    return b->s;
}

void lc_sb_free(lc_strbuf *b) { free(b->s); lc_sb_init(b); }
