/* latcalc -- internal growable string buffer (not part of the public API). */
#ifndef LATCALC_STRBUF_H
#define LATCALC_STRBUF_H

#include <stddef.h>

typedef struct {
    char *s;
    size_t len, cap;
    int failed;
} lc_strbuf;

void  lc_sb_init(lc_strbuf *b);
void  lc_sb_putc(lc_strbuf *b, char c);
void  lc_sb_puts(lc_strbuf *b, const char *s);
void  lc_sb_printf(lc_strbuf *b, const char *fmt, ...);
char *lc_sb_finish(lc_strbuf *b);   /* returns malloc'd string or NULL on failure */
void  lc_sb_free(lc_strbuf *b);

#endif
